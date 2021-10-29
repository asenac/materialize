// Copyright Materialize, Inc. and contributors. All rights reserved.
//
// Use of this software is governed by the Business Source License
// included in the LICENSE file.
//
// As of the Change Date specified in that file, in accordance with
// the Business Source License, use of this software will be governed
// by the Apache License, Version 2.0.

use crate::query_model::{
    BoxId, BoxType, ColumnReference, DistinctOperation, Expr, Model, Quantifier, QuantifierId,
    QuantifierSet, QuantifierType, QueryBox,
};
use itertools::Itertools;
use repr::RelationType;
use std::collections::{BTreeMap, HashMap, HashSet};

type ColumnMap = HashMap<ColumnReference, usize>;

impl Model {
    pub fn lower(&self) -> expr::MirRelationExpr {
        let mut lowerer = Lowerer::new(self);
        let mut id_gen = expr::IdGen::default();
        expr::MirRelationExpr::constant(vec![vec![]], RelationType::new(vec![]))
            .let_in(&mut id_gen, |id_gen, get_outer| {
                lowerer.apply(self.top_box, get_outer, &ColumnMap::new())
            })
    }
}

struct Lowerer<'a> {
    model: &'a Model,
}

impl<'a> Lowerer<'a> {
    fn new(model: &'a Model) -> Self {
        Self { model }
    }

    fn apply(
        &mut self,
        box_id: BoxId,
        get_outer: expr::MirRelationExpr,
        outer_column_map: &ColumnMap,
    ) -> expr::MirRelationExpr {
        use expr::MirRelationExpr as SR;
        let the_box = self.model.get_box(box_id).borrow();
        let mut input = match &the_box.box_type {
            BoxType::Values(values) => {
                let identity = SR::constant(vec![vec![]], RelationType::new(vec![]));
                // TODO(asenac) lower actual values
                assert!(values.rows.len() == 1 && the_box.columns.len() == 0);
                get_outer.product(identity)
            }
            BoxType::Select(select) => {
                let correlation_info = the_box.correlation_info(&self.model);
                if !correlation_info.is_empty() {
                    panic!("correlated joins are not supported yet");
                }

                let outer_arity = get_outer.arity();
                let mut input = self.lower_join(get_outer, outer_column_map, &the_box.quantifiers);
                let input_arity = input.arity();

                // generate a column map with the projection of the join
                let mut column_map = outer_column_map.clone();
                let mut next_column = outer_arity;
                for q_id in the_box.quantifiers.iter() {
                    let input_box = self.model.get_quantifier(*q_id).borrow().input_box;
                    let arity = self.model.get_box(input_box).borrow().columns.len();
                    for c in 0..arity {
                        column_map.insert(
                            ColumnReference {
                                quantifier_id: *q_id,
                                position: c,
                            },
                            next_column + c,
                        );
                    }

                    next_column += arity;
                }

                if !select.predicates.is_empty() {
                    input = input.filter(
                        select
                            .predicates
                            .iter()
                            .map(|p| Self::lower_expression(p, &column_map)),
                    );
                }

                if !the_box.columns.is_empty() {
                    input = input.map(
                        the_box
                            .columns
                            .iter()
                            .map(|c| Self::lower_expression(&c.expr, &column_map))
                            .collect_vec(),
                    );
                }

                // project the outer columns plus the ones in the projection of
                // this select box
                input.project(
                    (0..outer_arity)
                        .chain(input_arity..input_arity + the_box.columns.len())
                        .collect_vec(),
                )
            }
            _ => panic!(),
        };

        if the_box.distinct == DistinctOperation::Enforce {
            input = input.distinct();
        }

        input
    }

    fn lower_join(
        &mut self,
        get_outer: expr::MirRelationExpr,
        outer_column_map: &ColumnMap,
        quantifiers: &QuantifierSet,
    ) -> expr::MirRelationExpr {
        let outer_arity = get_outer.arity();

        // TODO(asenac) lower scalar subquery quantifiers
        assert!(quantifiers.iter().all(|q_id| {
            self.model.get_quantifier(*q_id).borrow().quantifier_type == QuantifierType::Foreach
        }));

        let join_inputs = quantifiers
            .iter()
            .map(|q_id| {
                let input_box = self.model.get_quantifier(*q_id).borrow().input_box;
                self.apply(input_box, get_outer.clone(), outer_column_map)
            })
            .collect_vec();

        if join_inputs.len() == 1 {
            join_inputs.into_iter().next().unwrap()
        } else {
            Self::join_on_prefix(join_inputs, outer_arity)
        }
    }

    fn join_on_prefix(
        join_inputs: Vec<expr::MirRelationExpr>,
        prefix_length: usize,
    ) -> expr::MirRelationExpr {
        let input_mapper = expr::JoinInputMapper::new(&join_inputs);
        // Join on the outer columns
        let equivalences = (0..prefix_length)
            .map(|col| {
                join_inputs
                    .iter()
                    .enumerate()
                    .map(|(input, _)| {
                        expr::MirScalarExpr::Column(input_mapper.map_column_to_global(col, input))
                    })
                    .collect_vec()
            })
            .collect_vec();
        // Project only one copy of the outer columns
        let projection = (0..prefix_length)
            .chain(
                join_inputs
                    .iter()
                    .enumerate()
                    .map(|(index, input)| {
                        (prefix_length..input.arity())
                            .map(|c| input_mapper.map_column_to_global(c, index))
                            .collect_vec()
                    })
                    .flatten(),
            )
            .collect_vec();
        expr::MirRelationExpr::join_scalars(join_inputs, equivalences).project(projection)
    }

    fn lower_expression(expr: &Expr, column_map: &ColumnMap) -> expr::MirScalarExpr {
        match expr {
            Expr::ColumnReference(c) => expr::MirScalarExpr::Column(*column_map.get(c).unwrap()),
            Expr::Literal(row, column_type) => {
                expr::MirScalarExpr::Literal(Ok(row.clone()), column_type.clone())
            }
            _ => panic!("unsupported expression"),
        }
    }
}
