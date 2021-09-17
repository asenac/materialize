// Copyright Materialize, Inc. and contributors. All rights reserved.
//
// Use of this software is governed by the Business Source License
// included in the LICENSE file.
//
// As of the Change Date specified in that file, in accordance with
// the Business Source License, use of this software will be governed
// by the Apache License, Version 2.0.

use crate::TransformArgs;

use expr::{BinaryFunc, IdGen, MirRelationExpr, MirScalarExpr};

#[derive(Debug)]
pub struct OuterJoinLowering;

impl crate::Transform for OuterJoinLowering {
    fn transform(
        &self,
        relation: &mut MirRelationExpr,
        args: TransformArgs,
    ) -> Result<(), crate::TransformError> {
        relation.visit_mut(&mut |e| self.action(e, args.id_gen));
        Ok(())
    }
}

impl OuterJoinLowering {
    fn action(&self, relation: &mut MirRelationExpr, id_gen: &mut IdGen) {
        match relation {
            MirRelationExpr::OuterJoin {
                preserving,
                non_preserving,
                predicates,
                product: _, // @todo
            } => {
                if let Some((l_keys, r_keys)) =
                    Self::is_equi_join(preserving, non_preserving, predicates)
                {
                    *relation = Self::plan_equi_join(
                        preserving.take_dangerous(),
                        non_preserving.take_dangerous(),
                        std::mem::replace(predicates, Vec::new()),
                        l_keys,
                        r_keys,
                        id_gen,
                    );
                } else {
                }
            }
            MirRelationExpr::FullOuterJoin { .. } => {}
            _ => {}
        }
    }

    fn is_equi_join(
        left: &MirRelationExpr,
        right: &MirRelationExpr,
        on: &Vec<MirScalarExpr>,
    ) -> Option<(Vec<usize>, Vec<usize>)> {
        let la = left.arity();
        let ra = right.arity();

        // @todo asenac canonicalize?
        // Deconstruct predicates that may be ands of multiple conditions.
        let mut predicates = Vec::new();
        let mut todo = on.clone();
        while let Some(next) = todo.pop() {
            if let MirScalarExpr::CallBinary {
                expr1,
                expr2,
                func: BinaryFunc::And,
            } = next
            {
                todo.push(*expr1);
                todo.push(*expr2);
            } else {
                predicates.push(next)
            }
        }

        // We restrict ourselves to predicates that test column equality between left and right.
        let mut l_keys = Vec::new();
        let mut r_keys = Vec::new();
        for predicate in predicates.iter_mut() {
            if let MirScalarExpr::CallBinary {
                expr1,
                expr2,
                func: BinaryFunc::Eq,
            } = predicate
            {
                if let (MirScalarExpr::Column(c1), MirScalarExpr::Column(c2)) =
                    (&mut **expr1, &mut **expr2)
                {
                    if *c1 > *c2 {
                        std::mem::swap(c1, c2);
                    }
                    if (*c1 < la) && (la <= *c2 && *c2 < la + ra) {
                        l_keys.push(*c1);
                        r_keys.push(*c2 - la);
                    }
                }
            }
        }
        // If any predicates were not column equivs, give up.
        if l_keys.len() < predicates.len() {
            None
        } else {
            Some((l_keys, r_keys))
        }
    }

    fn plan_equi_join(
        left: MirRelationExpr,
        right: MirRelationExpr,
        on: Vec<MirScalarExpr>,
        l_keys: Vec<usize>,
        r_keys: Vec<usize>,
        id_gen: &mut IdGen,
    ) -> MirRelationExpr {
        let la = left.arity();
        let ra = right.arity();
        let rt = right.typ();

        left.let_in(id_gen, |id_gen, get_left| {
            right.let_in(id_gen, |id_gen, get_right| {
                // TODO: we know that we can re-use the arrangements of left and right
                // needed for the inner join with each of the conditional outer joins.
                // It is not clear whether we should hint that, or just let the planner
                // and optimizer run and see what happens.

                // We'll want the inner join (minus repeated columns)
                let join =
                    expr::MirRelationExpr::join(vec![get_left.clone(), get_right.clone()], vec![])
                        // apply the filter constraints here, to ensure nulls are not matched.
                        .filter(on);

                // We'll want to re-use the results of the join multiple times.
                join.let_in(id_gen, |id_gen, get_join| {
                    let mut result = get_join.clone();

                    // A collection of keys present in both left and right collections.
                    let both_keys = get_join.project(l_keys.clone()).distinct();

                    // The plan is now to determine the left and right rows matched in the
                    // inner join, subtract them from left and right respectively, pad what
                    // remains with nulls, and fold them in to `result`.

                    both_keys.let_in(id_gen, |_id_gen, get_both| {
                        // Rows in `left` that are matched in the inner equijoin.
                        let left_present = expr::MirRelationExpr::join(
                            vec![get_left.clone(), get_both.clone()],
                            l_keys
                                .iter()
                                .enumerate()
                                .map(|(i, c)| vec![(0, *c), (1, i)])
                                .collect::<Vec<_>>(),
                        )
                        .project((0..la).collect());

                        // Determine the types of nulls to use as filler.
                        let right_fill = rt
                            .column_types
                            .into_iter()
                            .map(|typ| expr::MirScalarExpr::literal_null(typ.scalar_type))
                            .collect();

                        // Add to `result` absent elements, filled with typed nulls.
                        result = left_present
                            .negate()
                            .union(get_left.clone())
                            .map(right_fill)
                            .union(result);

                        result
                    })
                })
            })
        })
    }
}
