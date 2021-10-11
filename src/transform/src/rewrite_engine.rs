// Copyright Materialize, Inc. and contributors. All rights reserved.
//
// Use of this software is governed by the Business Source License
// included in the LICENSE file.
//
// As of the Change Date specified in that file, in accordance with
// the Business Source License, use of this software will be governed
// by the Apache License, Version 2.0.

//! Framework for rewriting expressions.

use std::cell::RefCell;

/// Trait that must be implemented for every expression type that supports
/// being transformed by this transform framework.
pub trait VisitMutExpr {
    fn visit_mut_pre_post_in<FnPre, FnPost, FnIn>(
        &mut self,
        pre: &mut FnPre,
        f_in: &mut FnIn,
        post: &mut FnPost,
    ) where
        FnPre: FnMut(&mut Self),
        FnIn: FnMut(&Self, usize),
        FnPost: FnMut(&mut Self);
}

/// Trait for visitors that perform mutation actions during a traversal of
/// the visitable expression.
///
/// `Data` contains the context information of the visitor.
pub trait MutExprVisitor<Expr: VisitMutExpr, Data: Default> {
    /// Invoked when entering the scope of the given expression.
    fn pre_visit(&self, _expr: &mut Expr, _data: &mut Data) {}

    /// Invoked after leaving the scope of a child expression and before entering
    /// the scope of the next child expression. Receives the index of the next
    /// child expression to be visited.
    fn in_visit(&self, _expr: &Expr, _input_idx: usize, _data: &mut Data) {}

    /// Invoked when leaving the scope of the given expression.
    fn post_visit(&self, _expr: &mut Expr, _data: &mut Data) {}
}

pub trait Transform<Expr> {
    fn apply_transforms(&self, expr: &mut Expr);
}

struct SingleTransform<Expr, Data> {
    transform: Box<dyn MutExprVisitor<Expr, Data>>,
}

impl<Expr, Data> Transform<Expr> for SingleTransform<Expr, Data>
where
    Data: Default,
    Expr: VisitMutExpr,
{
    /// Apply the list of tranformations to the given expression.
    fn apply_transforms(&self, expr: &mut Expr) {
        let data = RefCell::new(Default::default());
        expr.visit_mut_pre_post_in(
            &mut |e| self.transform.pre_visit(e, &mut data.borrow_mut()),
            &mut |e, input_idx| {
                self.transform
                    .in_visit(e, input_idx, &mut data.borrow_mut());
            },
            &mut |e| {
                self.transform.post_visit(e, &mut data.borrow_mut());
            },
        );
    }
}

/// A list of transformations, represented as `MutExprVisitor`, that can be
/// applied during the same graph traversal. They all must accept the same
/// data type.
struct CombinedTransforms<Expr, Data>
where
    Data: Default,
    Expr: VisitMutExpr,
{
    transforms: Vec<Box<dyn MutExprVisitor<Expr, Data>>>,
}

impl<Expr, Data> Transform<Expr> for CombinedTransforms<Expr, Data>
where
    Data: Default,
    Expr: VisitMutExpr,
{
    /// Apply the list of tranformations to the given expression.
    fn apply_transforms(&self, expr: &mut Expr) {
        let data = RefCell::new(Default::default());
        expr.visit_mut_pre_post_in(
            &mut |e| {
                for t in self.transforms.iter() {
                    t.pre_visit(e, &mut data.borrow_mut());
                }
            },
            &mut |e, input_idx| {
                for t in self.transforms.iter() {
                    t.in_visit(e, input_idx, &mut data.borrow_mut());
                }
            },
            &mut |e| {
                for t in self.transforms.iter() {
                    t.post_visit(e, &mut data.borrow_mut());
                }
            },
        );
    }
}

use expr::MirRelationExpr;

impl VisitMutExpr for MirRelationExpr {
    fn visit_mut_pre_post_in<FnPre, FnPost, FnIn>(
        &mut self,
        pre: &mut FnPre,
        f_in: &mut FnIn,
        post: &mut FnPost,
    ) where
        FnPre: FnMut(&mut Self),
        FnIn: FnMut(&Self, usize),
        FnPost: FnMut(&mut Self),
    {
        pre(self);

        match self {
            MirRelationExpr::Constant { .. } | MirRelationExpr::Get { .. } => (),
            MirRelationExpr::Let { value, body, .. } => {
                value.visit_mut_pre_post_in(pre, f_in, post);
                f_in(self, 1);
                body.visit_mut_pre_post_in(pre, f_in, post);
            }
            MirRelationExpr::Project { input, .. } => {
                input.visit_mut_pre_post_in(pre, f_in, post);
            }
            MirRelationExpr::Map { input, .. } => {
                input.visit_mut_pre_post_in(pre, f_in, post);
            }
            MirRelationExpr::FlatMap { input, .. } => {
                input.visit_mut_pre_post_in(pre, f_in, post);
            }
            MirRelationExpr::Filter { input, .. } => {
                input.visit_mut_pre_post_in(pre, f_in, post);
            }
            MirRelationExpr::Join { inputs, .. } => {
                let num_inputs = inputs.len();
                for (input_idx, input) in inputs.iter_mut().enumerate() {
                    input.visit_mut_pre_post_in(pre, f_in, post);
                    if input_idx + 1 < num_inputs {
                        f_in(self, input_idx + 1);
                    }
                }
            }
            MirRelationExpr::Reduce { input, .. } => {
                input.visit_mut_pre_post_in(pre, f_in, post);
            }
            MirRelationExpr::TopK { input, .. } => {
                input.visit_mut_pre_post_in(pre, f_in, post);
            }
            MirRelationExpr::Negate { input } => input.visit_mut_pre_post_in(pre, f_in, post),
            MirRelationExpr::Threshold { input } => input.visit_mut_pre_post_in(pre, f_in, post),
            MirRelationExpr::Union { base, inputs } => {
                base.visit_mut_pre_post_in(pre, f_in, post);
                for (input_idx, input) in inputs.iter_mut().enumerate() {
                    f_in(self, input_idx + 1);
                    input.visit_mut_pre_post_in(pre, f_in, post);
                }
            }
            MirRelationExpr::ArrangeBy { input, .. } => {
                input.visit_mut_pre_post_in(pre, f_in, post);
            }
            MirRelationExpr::DeclareKeys { input, .. } => {
                input.visit_mut_pre_post_in(pre, f_in, post);
            }
        }

        post(self);
    }
}
