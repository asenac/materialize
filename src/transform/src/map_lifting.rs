// Copyright Materialize, Inc. All rights reserved.
//
// Use of this software is governed by the Business Source License
// included in the LICENSE file.
//
// As of the Change Date specified in that file, in accordance with
// the Business Source License, use of this software will be governed
// by the Apache License, Version 2.0.

//! Hoist literal values from maps wherever possible.
//!
//! This transform specifically looks for `MirRelationExpr::Map` operators
//! where any of the `ScalarExpr` expressions are literals. Whenever it
//! can, it lifts those expressions through or around operators.
//!
//! The main feature of this operator is that it allows transformations
//! to locally change the shape of operators, presenting fewer columns
//! when they are unused and replacing them with mapped default values.
//! The mapped default values can then be lifted and ideally absorbed.
//! This type of transformation is difficult to make otherwise, as it
//! is not easy to locally change the shape of relations.

use std::collections::HashMap;

use expr::{Id, JoinInputMapper, MirRelationExpr, MirScalarExpr};

use itertools::Itertools;
use repr::Row;

use crate::TransformArgs;

/// Hoist literal values from maps wherever possible.
#[derive(Debug)]
pub struct LiteralLifting;

impl crate::Transform for LiteralLifting {
    fn transform(
        &self,
        relation: &mut MirRelationExpr,
        _: TransformArgs,
    ) -> Result<(), crate::TransformError> {
        // TODO(asenac) materialize literals?
        let _ = self.action(relation, &mut HashMap::new());
        Ok(())
    }
}

type LiteralMap = HashMap<usize, MirScalarExpr>;

impl LiteralLifting {
    /// Hoist literal values from maps wherever possible.
    ///
    /// Returns a list of literal scalar expressions that must be appended
    /// to the result before it can be correctly used. The intent is that
    /// this action extracts a maximal set of literals from `relation`,
    /// which can then often be propagated further up and inlined in any
    /// expressions as it goes.
    ///
    /// In several cases, we only manage to extract literals from the final
    /// columns. But in those cases where it is possible, permutations are
    /// used to move all of the literals to the final columns, and then rely
    /// on projection hoisting to allow the these literals to move up the AST.
    ///
    /// TODO: The literals from the final columns are returned as the result
    /// of this method, whereas literals in intermediate columns are extracted
    /// using permutations. The reason for this different treatment is that in
    /// some cases it is not possible to remove the projection of the
    /// permutation, preventing the lifting of a literal that could otherwise
    /// be lifted, the following example being of them:
    ///
    /// %0 =
    /// | Constant (1, 2, 3) (2, 2, 3)
    ///
    /// %1 =
    /// | Constant (4, 3, 3) (4, 5, 3)
    ///
    /// %2 =
    /// | Union %0 %1
    ///
    /// If final literals weren't treated differently, the example above would
    /// lead to the following transformed plan:
    ///
    /// %0 =
    /// | Constant (1) (2)
    /// | Map 2, 3
    /// | Project (#0..#2)
    ///
    /// %1 =
    /// | Constant (3) (5)
    /// | Map 4, 3
    /// | Project (#1, #0, #2)
    ///
    /// %2 =
    /// | Union %0 %1
    ///
    /// Since the union branches have different projections, they cannot be
    /// removed, preventing literal 3 from being lifted further.
    ///
    /// In theory, all literals could be treated in the same way if this method
    /// returned both a list of literals and a projection vector, making the
    /// caller have to deal with the reshuffling.
    /// (see https://github.com/MaterializeInc/materialize/issues/6598)
    ///
    pub fn action(
        &self,
        relation: &mut MirRelationExpr,
        // Map from names to literals required for appending.
        gets: &mut HashMap<Id, LiteralMap>,
    ) -> LiteralMap {
        match relation {
            MirRelationExpr::Constant { rows, typ } => {
                // From the back to the front, check if all values are identical.
                let mut the_same = vec![true; typ.arity()];
                if let Ok([(row, _cnt), rows @ ..]) = rows.as_deref_mut() {
                    let data = row.unpack();
                    assert_eq!(the_same.len(), data.len());
                    for (row, _cnt) in rows.iter() {
                        let other = row.unpack();
                        assert_eq!(the_same.len(), other.len());
                        for index in 0..the_same.len() {
                            the_same[index] = the_same[index] && (data[index] == other[index]);
                        }
                    }

                    // Any subset of constant values can be extracted with a permute.
                    let common_literals = the_same.iter().filter(|e| **e).count();
                    if common_literals > 0 {
                        let final_arity = the_same.len() - common_literals;
                        let mut projected_literals = Vec::new();
                        let mut projection = Vec::new();
                        let mut new_column_types = Vec::new();
                        for (i, sameness) in the_same.iter().enumerate() {
                            if *sameness {
                                projection.push(final_arity + projected_literals.len());
                                projected_literals.push(MirScalarExpr::literal_ok(
                                    data[i],
                                    typ.column_types[i].scalar_type.clone(),
                                ));
                            } else {
                                projection.push(new_column_types.len());
                                new_column_types.push(typ.column_types[i].clone());
                            }
                        }
                        typ.column_types = new_column_types;

                        // Tidy up the type information of `relation`.
                        for key in typ.keys.iter_mut() {
                            *key = key
                                .iter()
                                .filter(|x| !the_same[**x])
                                .map(|x| projection[*x])
                                .collect::<Vec<usize>>();
                        }
                        typ.keys.sort();
                        typ.keys.dedup();

                        let remove_extracted_literals = |row: &mut Row| {
                            let mut new_row = Row::default();
                            let data = row.unpack();
                            for i in 0..the_same.len() {
                                if !the_same[i] {
                                    new_row.push(data[i]);
                                }
                            }
                            *row = new_row;
                        };

                        remove_extracted_literals(row);
                        for (row, _cnt) in rows.iter_mut() {
                            remove_extracted_literals(row);
                        }

                        return Self::add_permute(
                            relation,
                            final_arity,
                            projected_literals,
                            projection,
                        );
                    }
                }

                HashMap::new()
            }
            MirRelationExpr::Get { id, typ: _ } => {
                // A get expression may need to have literal expressions appended to it.
                let literals = gets.get(id).cloned().unwrap_or_else(HashMap::new);
                // if !literals.is_empty() {
                //     // Correct the type of the `Get`, which has fewer columns,
                //     // and not the same fields in its keys. It is ok to remove
                //     // any columns from the keys, as them being literals meant
                //     // that their distinctness was not what made anything a key.
                //     for _ in 0..literals.len() {
                //         typ.column_types.pop();
                //     }
                //     let columns = typ.column_types.len();
                //     for key in typ.keys.iter_mut() {
                //         key.retain(|k| k < &columns);
                //     }
                //     typ.keys.sort();
                //     typ.keys.dedup();
                // }
                literals
            }
            MirRelationExpr::Let { id, value, body } => {
                // Any literals appended to the `value` should be used
                // at corresponding `Get`s throughout the `body`.
                let literals = self.action(value, gets);
                let id = Id::Local(*id);
                if !literals.is_empty() {
                    let prior = gets.insert(id, literals);
                    assert!(!prior.is_some());
                }
                let result = self.action(body, gets);
                gets.remove(&id);
                result
            }
            MirRelationExpr::Project { input, outputs } => {
                let literals = self.action(input, gets);

                // Generate a new map with the new indices
                outputs
                    .iter()
                    .enumerate()
                    .filter_map(|(i, x)| {
                        if let Some(l) = literals.get(x) {
                            Some((i, l.clone()))
                        } else {
                            None
                        }
                    })
                    .collect::<LiteralMap>()
            }
            MirRelationExpr::Map { input, scalars } => {
                let mut literals = self.action(input, gets);
                let input_arity = input.arity();

                // Add the literals added by this operator to the map
                for (i, scalar) in scalars.iter_mut().enumerate() {
                    if scalar.is_literal() {
                        literals.insert(i + input_arity, scalar.clone());
                    } else {
                        // Propagate literals through expressions and remap columns.
                        Self::propagate_literals(scalar, &literals);
                    }
                }

                literals
            }
            MirRelationExpr::FlatMap {
                input,
                func: _,
                exprs,
                demand: _,
            } => {
                let literals = self.action(input, gets);
                if !literals.is_empty() {
                    for expr in exprs.iter_mut() {
                        Self::propagate_literals(expr, &literals);
                    }
                }
                LiteralMap::new()
            }
            MirRelationExpr::Filter { input, predicates } => {
                let literals = self.action(input, gets);
                if !literals.is_empty() {
                    // We should be able to instantiate all uses of `literals`
                    // in predicates and then lift the `map` around the filter.
                    for expr in predicates.iter_mut() {
                        Self::propagate_literals(expr, &literals);
                    }
                }
                literals
            }
            MirRelationExpr::Join {
                inputs,
                equivalences,
                demand,
                implementation,
            } => {
                let input_mapper = JoinInputMapper::new(inputs);

                // lift literals from each input
                let mut input_literals = Vec::new();
                for input in inputs.iter_mut() {
                    input_literals.push(self.action(input, gets));
                }

                let literals: LiteralMap = input_literals
                    .iter_mut()
                    .enumerate()
                    .map(|(input, literals)| {
                        literals
                            .drain()
                            .map(|(col, l)| (input_mapper.map_column_to_global(col, input), l))
                            .collect::<Vec<_>>()
                    })
                    .flatten()
                    .collect();

                if !literals.is_empty() {
                    *demand = None;
                    *implementation = expr::JoinImplementation::Unimplemented;

                    // Visit each expression in each equivalence class to inline
                    // literals
                    for equivalence in equivalences.iter_mut() {
                        for expr in equivalence.iter_mut() {
                            Self::propagate_literals(expr, &literals);
                        }
                    }
                }

                literals
            }
            MirRelationExpr::Reduce {
                input,
                group_key,
                aggregates,
                monotonic: _,
                expected_group_size: _,
            } => {
                let literals = self.action(input, gets);
                if !literals.is_empty() {
                    // Inline literals into group key expressions.
                    for expr in group_key.iter_mut() {
                        Self::propagate_literals(expr, &literals);
                    }
                    // Inline literals into aggregate value selector expressions.
                    for aggr in aggregates.iter_mut() {
                        Self::propagate_literals(&mut aggr.expr, &literals);
                    }
                }

                // The only literals we think we can lift are those that are
                // independent of the number of records; things like `Any`, `All`,
                // `Min`, and `Max`.
                let eval_constant_aggr = |aggr: &expr::AggregateExpr| {
                    let temp = repr::RowArena::new();
                    let eval = aggr
                        .func
                        .eval(Some(aggr.expr.eval(&[], &temp).unwrap()), &temp);
                    MirScalarExpr::literal_ok(
                        eval,
                        // This type information should be available in the `a.expr` literal,
                        // but extracting it with pattern matching seems awkward.
                        aggr.func
                            .output_type(aggr.expr.typ(&repr::RelationType::empty()))
                            .scalar_type,
                    )
                };

                // Add a Map operator with the remaining literals so that they are lifted in
                // the next invocation of this transform.
                let non_literal_keys = group_key.iter().filter(|x| !x.is_literal()).count();
                let non_constant_aggr = aggregates.iter().filter(|x| !x.is_constant()).count();
                if non_literal_keys != group_key.len() || non_constant_aggr != aggregates.len() {
                    let first_projected_literal: usize = non_literal_keys + non_constant_aggr;
                    let mut projection = Vec::new();
                    let mut projected_literals = Vec::new();

                    let mut new_group_key = Vec::new();
                    for key in group_key.drain(..) {
                        if key.is_literal() {
                            projection.push(first_projected_literal + projected_literals.len());
                            projected_literals.push(key);
                        } else {
                            projection.push(new_group_key.len());
                            new_group_key.push(key);
                        }
                    }
                    // The new group key without literals
                    *group_key = new_group_key;

                    let mut new_aggregates = Vec::new();
                    for aggr in aggregates.drain(..) {
                        if aggr.is_constant() {
                            projection.push(first_projected_literal + projected_literals.len());
                            projected_literals.push(eval_constant_aggr(&aggr));
                        } else {
                            projection.push(group_key.len() + new_aggregates.len());
                            new_aggregates.push(aggr);
                        }
                    }
                    // The new aggregates without constant ones
                    *aggregates = new_aggregates;

                    return Self::add_permute(
                        relation,
                        first_projected_literal,
                        projected_literals,
                        projection,
                    );
                }

                LiteralMap::new()
            }
            MirRelationExpr::TopK {
                input,
                group_key,
                order_key,
                limit: _,
                offset: _,
                monotonic: _,
            } => {
                let literals = self.action(input, gets);
                if !literals.is_empty() {
                    // TODO(asenac)
                    // We should be able to lift literals out, as they affect neither
                    // grouping nor ordering. We should discard grouping and ordering
                    // that references the columns, though.
                    let input_arity = input.arity();
                    group_key.retain(|c| *c < input_arity);
                    order_key.retain(|o| o.column < input_arity);
                }
                literals
            }
            MirRelationExpr::Negate { input } => {
                // Literals can just be lifted out of negate.
                self.action(input, gets)
            }
            MirRelationExpr::Threshold { input } => {
                // Literals can just be lifted out of threshold.
                self.action(input, gets)
            }
            MirRelationExpr::DeclareKeys { input, .. } => self.action(input, gets),
            MirRelationExpr::Union { base, inputs } => {
                let mut base_literals = self.action(base, gets);
                let input_literals = inputs
                    .iter_mut()
                    .map(|input| self.action(input, gets))
                    .collect::<Vec<LiteralMap>>();

                let common_literals = base_literals
                    .drain()
                    .filter(|(i, x)| input_literals.iter().all(|m| m.get(i) == Some(x)))
                    .collect::<LiteralMap>();

                if !common_literals.is_empty() {
                    // Add a projection discarding the literals on top of each branch
                    let input_arity = base.arity();
                    let reduced_projection = (0..input_arity)
                        .filter(|x| !common_literals.contains_key(x))
                        .collect::<Vec<_>>();
                    let final_union_arity = reduced_projection.len();

                    for input in inputs.iter_mut() {
                        *input = input.take_dangerous().project(reduced_projection.clone());
                    }

                    **base = base.take_dangerous().project(reduced_projection);

                    // Re-add the literals using a permute
                    let mut literals = Vec::new();
                    let mut projection = Vec::new();
                    for i in 0..input_arity {
                        if let Some(literal) = common_literals.get(&i) {
                            projection.push(final_union_arity + literals.len());
                            literals.push(literal.clone());
                        } else {
                            projection.push(projection.len());
                        }
                    }

                    Self::add_permute(relation, final_union_arity, literals, projection)
                } else {
                    common_literals
                }
            }
            MirRelationExpr::ArrangeBy { input, keys } => {
                // TODO(frank): Not sure if this is the right behavior,
                // as we disrupt the set of used arrangements. Though,
                // we are probably most likely to use arranged `Get`
                // operators rather than those decorated with maps.
                let literals = self.action(input, gets);
                if !literals.is_empty() {
                    for key in keys.iter_mut() {
                        for expr in key.iter_mut() {
                            Self::propagate_literals(expr, &literals);
                        }
                    }
                }
                literals
            }
        }
    }

    /// Adds a permute on top of the given relation
    fn add_permute(
        relation: &mut MirRelationExpr,
        input_arity: usize,
        mut scalars: Vec<MirScalarExpr>,
        mut projection: Vec<usize>,
    ) -> LiteralMap {
        // Remove scalars not referenced in the projection
        if !scalars.is_empty() {
            let mut used_scalars = projection
                .iter()
                .enumerate()
                .filter(|(_, x)| **x >= input_arity)
                .map(|(out_col, old_in_col)| (old_in_col - input_arity, out_col))
                // group them to avoid adding duplicated literals
                .into_group_map()
                .drain()
                .collect::<Vec<_>>();

            if used_scalars.len() != scalars.len() {
                used_scalars.sort();
                // Discard literals that are not projected
                scalars = used_scalars
                    .iter()
                    .map(|(old_in_col, _)| scalars[*old_in_col].clone())
                    .collect::<Vec<_>>();
                // Update the references to the literal in the projection
                for (new_in_col, (_old_in_col, out_cols)) in used_scalars.iter().enumerate() {
                    for out_col in out_cols {
                        projection[*out_col] = input_arity + new_in_col;
                    }
                }
            }
        }

        let literal_map: LiteralMap = projection
            .iter()
            .enumerate()
            .filter(|(_, x)| **x >= input_arity)
            .map(|(i, x)| (i, scalars[*x - input_arity].clone()))
            .collect();

        let projection_input_arity = input_arity + scalars.len();

        if !scalars.is_empty() {
            if let MirRelationExpr::Map {
                input: _,
                scalars: inner_scalars,
            } = relation
            {
                inner_scalars.extend(scalars);
            } else {
                *relation = relation.take_dangerous().map(scalars);
            }
        }

        Self::add_projection_if_needed(relation, projection_input_arity, projection);

        literal_map
    }

    fn add_projection_if_needed(
        relation: &mut MirRelationExpr,
        input_arity: usize,
        projection: Vec<usize>,
    ) {
        if input_arity != projection.len() || projection.iter().enumerate().any(|(i, x)| i != *x) {
            *relation = relation.take_dangerous().project(projection);
        }
    }

    fn propagate_literals(scalar: &mut MirScalarExpr, literals: &LiteralMap) {
        scalar.visit_mut(&mut |e| {
            if let MirScalarExpr::Column(id) = e {
                if let Some(l) = literals.get(id) {
                    *e = l.clone();
                }
            }
        });
    }
}
