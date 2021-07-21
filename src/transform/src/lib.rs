// Copyright Materialize, Inc. and contributors. All rights reserved.
//
// Use of this software is governed by the Business Source License
// included in the LICENSE file.
//
// As of the Change Date specified in that file, in accordance with
// the Business Source License, use of this software will be governed
// by the Apache License, Version 2.0.

//! Transformations for relation expressions.
//!
//! This crate contains traits, types, and methods suitable for transforming
//! `MirRelationExpr` types in ways that preserve semantics and improve performance.
//! The core trait is `Transform`, and many implementors of this trait can be
//! boxed and iterated over. Some common transformation patterns are wrapped
//! as `Transform` implementors themselves.
//!
//! The crate also contains the beginnings of whole-dataflow optimization,
//! which uses the same analyses but spanning multiple dataflow elements.

#![forbid(missing_docs)]
#![deny(missing_debug_implementations)]

use std::collections::HashMap;
use std::error::Error;
use std::fmt;

use expr::MirRelationExpr;
use expr::MirScalarExpr;
use expr::{GlobalId, IdGen};

pub mod column_knowledge;
pub mod cse;
pub mod demand;
pub mod fusion;
pub mod inline_let;
pub mod join_implementation;
pub mod map_lifting;
pub mod nonnull_requirements;
pub mod nonnullable;
pub mod predicate_pushdown;
pub mod projection_extraction;
pub mod projection_lifting;
pub mod reduce_elision;
pub mod reduction;
pub mod reduction_pushdown;
pub mod redundant_join;
pub mod topk_elision;
pub mod union_cancel;
pub mod update_let;

pub mod dataflow;
pub use dataflow::optimize_dataflow;

/// Arguments that get threaded through all transforms.
#[derive(Debug)]
pub struct TransformArgs<'a> {
    /// A shared instance of IdGen to allow constructing new Let expressions.
    pub id_gen: &'a mut IdGen,
    /// The indexes accessible.
    pub indexes: &'a HashMap<GlobalId, Vec<(GlobalId, Vec<MirScalarExpr>)>>,
}

/// Types capable of transforming relation expressions.
pub trait Transform: std::fmt::Debug {
    /// Transform a relation into a functionally equivalent relation.
    fn transform(
        &self,
        relation: &mut MirRelationExpr,
        args: TransformArgs,
    ) -> Result<(), TransformError>;
    /// A string describing the transform.
    ///
    /// This is useful mainly when iterating through many `Box<Tranform>`
    /// and one wants to judge progress before some defect occurs.
    fn debug(&self) -> String {
        format!("{:?}", self)
    }
}

/// doc me
#[derive(Debug)]
pub enum Traversal {
    /// doc me
    PostOrder,
    /// doc me
    PreOrder,
}

/// Transforms that can be applied locally to a single node.
pub trait LocalTransform: std::fmt::Debug {
    /// doc me
    fn action(
        &self,
        relation: &mut MirRelationExpr,
        args: &TransformArgs,
        cache: &mut Option<Box<dyn LocalTransformCache>>,
    );
}

/// doc me
pub trait LocalTransformCache {}

/// doc me
#[derive(Debug)]
pub struct TraverseAndTransform {
    /// Note: the constructor validates that all transforms support
    /// this traversal order
    traversal: Traversal,
    transforms: Vec<Box<dyn LocalTransform + Send>>,
}

impl Transform for TraverseAndTransform {
    fn transform(
        &self,
        relation: &mut MirRelationExpr,
        args: TransformArgs,
    ) -> Result<(), TransformError> {
        let mut caches: Vec<Option<Box<dyn LocalTransformCache>>> =
            (0..self.transforms.len()).map(|_| None).collect();
        match &self.traversal {
            Traversal::PreOrder => relation.visit_mut_pre(&mut |r| {
                for (transform, cache) in self.transforms.iter().zip(caches.iter_mut()) {
                    transform.action(r, &args, cache);
                }
            }),
            Traversal::PostOrder => relation.visit_mut(&mut |r| {
                for (transform, cache) in self.transforms.iter().zip(caches.iter_mut()) {
                    transform.action(r, &args, cache);
                }
            }),
        }
        Ok(())
    }
}

/// Errors that can occur during a transformation.
#[derive(Debug, Clone)]
pub enum TransformError {
    /// An unstructured error.
    Internal(String),
}

impl fmt::Display for TransformError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            TransformError::Internal(msg) => write!(f, "internal transform error: {}", msg),
        }
    }
}

impl Error for TransformError {}

/// A sequence of transformations iterated some number of times.
#[derive(Debug)]
pub struct Fixpoint {
    transforms: Vec<Box<dyn crate::Transform + Send>>,
    limit: usize,
}

impl Transform for Fixpoint {
    fn transform(
        &self,
        relation: &mut MirRelationExpr,
        args: TransformArgs,
    ) -> Result<(), TransformError> {
        for _ in 0..self.limit {
            let original = relation.clone();
            for transform in self.transforms.iter() {
                transform.transform(
                    relation,
                    TransformArgs {
                        id_gen: args.id_gen,
                        indexes: args.indexes,
                    },
                )?;
            }
            if *relation == original {
                return Ok(());
            }
        }
        let original = relation.clone();
        for transform in self.transforms.iter() {
            transform.transform(
                relation,
                TransformArgs {
                    id_gen: args.id_gen,
                    indexes: args.indexes,
                },
            )?;
        }
        Err(TransformError::Internal(format!(
            "fixpoint looped too many times {:#?} {}\n{}",
            self,
            original.pretty(),
            relation.pretty()
        )))
    }
}

/// A sequence of transformations that simplify the `MirRelationExpr`
#[derive(Debug)]
pub struct FuseAndCollapse {
    transforms: Vec<Box<dyn crate::Transform + Send>>,
}

impl Default for FuseAndCollapse {
    fn default() -> Self {
        Self {
            // TODO: The relative orders of the transforms have not been
            // determined except where there are comments.
            // TODO (#6542): All the transforms here except for
            // `ProjectionLifting`, `InlineLet`, `UpdateLet`, and
            // `RedundantJoin` can be implemented as free functions. Note that
            // (#716) proposes the removal of `InlineLet` and `UpdateLet` as a
            // transforms.
            transforms: vec![
                Box::new(TraverseAndTransform {
                    traversal: Traversal::PostOrder,
                    transforms: vec![Box::new(crate::projection_extraction::ProjectionExtraction)],
                }),
                Box::new(crate::inline_let::InlineLet),
                Box::new(crate::projection_lifting::ProjectionLifting),
                Box::new(TraverseAndTransform {
                    traversal: Traversal::PostOrder,
                    transforms: vec![
                        Box::new(crate::fusion::map::Map),
                        Box::new(crate::fusion::filter::Filter),
                        Box::new(crate::fusion::project::Project),
                        Box::new(crate::fusion::join::Join),
                        Box::new(crate::fusion::reduce::Reduce),
                        Box::new(crate::fusion::union::Union),
                        // This goes after union fusion so we can cancel out
                        // more branches at a time.
                        Box::new(crate::union_cancel::UnionBranchCancellation),
                    ],
                }),
                // This should run before redundant join to ensure that key info
                // is correct.
                Box::new(crate::update_let::UpdateLet),
                // Removes redundant inputs from joins.
                // Note that this eliminates one redundant input per join,
                // so it is necessary to run this section in a loop.
                // TODO: (#6748) Predicate pushdown unlocks the ability to
                // remove some redundant joins but also prevents other
                // redundant joins from being removed. When predicate pushdown
                // no longer works against redundant join, check if it is still
                // necessary to run RedundantJoin here.
                Box::new(crate::redundant_join::RedundantJoin),
                // As a final logical action, convert any constant expression to a constant.
                // Some optimizations fight against this, and we want to be sure to end as a
                // `MirRelationExpr::Constant` if that is the case, so that subsequent use can
                // clearly see this.
                Box::new(TraverseAndTransform {
                    traversal: Traversal::PostOrder,
                    transforms: vec![Box::new(crate::reduction::FoldConstants)],
                }),
            ],
        }
    }
}

impl Transform for FuseAndCollapse {
    fn transform(
        &self,
        relation: &mut MirRelationExpr,
        args: TransformArgs,
    ) -> Result<(), TransformError> {
        for transform in self.transforms.iter() {
            transform.transform(
                relation,
                TransformArgs {
                    id_gen: args.id_gen,
                    indexes: args.indexes,
                },
            )?;
        }
        Ok(())
    }
}

/// A naive optimizer for relation expressions.
///
/// The optimizer currently applies only peep-hole optimizations, from a limited
/// set that were sufficient to get some of TPC-H up and working. It is worth a
/// review at some point to improve the quality, coverage, and architecture of
/// the optimizations.
#[derive(Debug)]
pub struct Optimizer {
    /// The list of transforms to apply to an input relation.
    pub transforms: Vec<Box<dyn crate::Transform + Send>>,
}

impl Optimizer {
    /// Optimizes the supplied relation expression.
    fn transform(
        &self,
        relation: &mut MirRelationExpr,
        indexes: &HashMap<GlobalId, Vec<(GlobalId, Vec<MirScalarExpr>)>>,
    ) -> Result<(), TransformError> {
        let mut id_gen = Default::default();
        for transform in self.transforms.iter() {
            transform.transform(
                relation,
                TransformArgs {
                    id_gen: &mut id_gen,
                    indexes,
                },
            )?;
        }
        Ok(())
    }
}

impl Default for Optimizer {
    fn default() -> Self {
        let transforms: Vec<Box<dyn crate::Transform + Send>> = vec![
            // 1. Structure-agnostic cleanup
            Box::new(TraverseAndTransform {
                traversal: Traversal::PostOrder,
                transforms: vec![Box::new(crate::topk_elision::TopKElision)],
            }),
            Box::new(crate::nonnull_requirements::NonNullRequirements),
            // 2. Collapse constants, joins, unions, and lets as much as possible.
            // TODO: lift filters/maps to maximize ability to collapse
            // things down?
            Box::new(crate::Fixpoint {
                limit: 100,
                transforms: vec![Box::new(crate::FuseAndCollapse::default())],
            }),
            // 3. Move predicate information up and down the tree.
            //    This also fixes the shape of joins in the plan.
            Box::new(crate::Fixpoint {
                limit: 100,
                transforms: vec![
                    // Predicate pushdown sets the equivalence classes of joins.
                    Box::new(crate::predicate_pushdown::PredicatePushdown),
                    // Lifts the information `!isnull(col)`
                    Box::new(TraverseAndTransform {
                        traversal: Traversal::PostOrder,
                        transforms: vec![Box::new(crate::nonnullable::NonNullable)],
                    }),
                    // Lifts the information `col = literal`
                    // TODO (#6613): this also tries to lift `!isnull(col)` but
                    // less well than the previous transform. Eliminate
                    // redundancy between the two transforms.
                    Box::new(crate::column_knowledge::ColumnKnowledge),
                    // Lifts the information `col1 = col2`
                    Box::new(crate::demand::Demand),
                    Box::new(crate::FuseAndCollapse::default()),
                ],
            }),
            // 4. Reduce/Join simplifications.
            Box::new(crate::Fixpoint {
                limit: 100,
                transforms: vec![
                    Box::new(TraverseAndTransform {
                        traversal: Traversal::PostOrder,
                        transforms: vec![
                            // Pushes aggregations down
                            Box::new(crate::reduction_pushdown::ReductionPushdown),
                            // Replaces reduces with maps when the group keys are
                            // unique with maps
                            Box::new(crate::reduce_elision::ReduceElision),
                        ],
                    }),
                    // Converts `Cross Join {Constant(Literal) + Input}` to
                    // `Map {Cross Join (Input, Constant()), Literal}`.
                    // Join fusion will clean this up to `Map{Input, Literal}`
                    Box::new(crate::map_lifting::LiteralLifting),
                    Box::new(crate::FuseAndCollapse::default()),
                ],
            }),
            // Logical transforms are above this line. Physical transforms are
            // below this line.
            // TODO: split these transforms into two sets so that physical
            // transforms only run once?
            // Implementation transformations
            Box::new(crate::Fixpoint {
                limit: 100,
                transforms: vec![
                    Box::new(crate::projection_lifting::ProjectionLifting),
                    Box::new(crate::join_implementation::JoinImplementation),
                    Box::new(crate::column_knowledge::ColumnKnowledge),
                    Box::new(TraverseAndTransform {
                        traversal: Traversal::PostOrder,
                        transforms: vec![
                            Box::new(crate::reduction::FoldConstants),
                            Box::new(crate::fusion::filter::Filter),
                        ],
                    }),
                    // fill in the new demand after maps have been shifted
                    // around.
                    Box::new(crate::demand::Demand),
                    Box::new(crate::map_lifting::LiteralLifting),
                    Box::new(TraverseAndTransform {
                        traversal: Traversal::PostOrder,
                        transforms: vec![Box::new(crate::fusion::map::Map)],
                    }),
                ],
            }),
            Box::new(TraverseAndTransform {
                traversal: Traversal::PostOrder,
                transforms: vec![
                    Box::new(crate::reduction_pushdown::ReductionPushdown),
                    Box::new(crate::cse::map::Map),
                ],
            }),
            Box::new(crate::projection_lifting::ProjectionLifting),
            Box::new(crate::join_implementation::JoinImplementation),
            Box::new(TraverseAndTransform {
                traversal: Traversal::PostOrder,
                transforms: vec![
                    Box::new(crate::fusion::project::Project),
                    Box::new(crate::reduction::FoldConstants),
                ],
            }),
        ];
        Self { transforms }
    }
}

impl Optimizer {
    /// Optimizes the supplied relation expression.
    pub fn optimize(
        &mut self,
        mut relation: MirRelationExpr,
        indexes: &HashMap<GlobalId, Vec<(GlobalId, Vec<MirScalarExpr>)>>,
    ) -> Result<expr::OptimizedMirRelationExpr, TransformError> {
        self.transform(&mut relation, indexes)?;
        Ok(expr::OptimizedMirRelationExpr(relation))
    }
}
