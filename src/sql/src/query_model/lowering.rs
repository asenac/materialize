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
    QuantifierType, QueryBox,
};
use repr::{RelationType, ScalarType};
use std::cell::RefCell;
use std::collections::{BTreeMap, HashMap, HashSet};

impl Model {
    pub fn lower(&self) -> expr::MirRelationExpr {
        let mut id_gen = expr::IdGen::default();
        expr::MirRelationExpr::constant(vec![vec![]], RelationType::new(vec![])).let_in(
            &mut id_gen,
            |id_gen, get_outer| {
                let empty = Vec::new();
                let mut lowered_boxes = HashMap::new();
                self.get_box(self.top_box).borrow().applied_to(
                    self,
                    id_gen,
                    &mut lowered_boxes,
                    get_outer,
                    &empty,
                )
            },
        )
    }
}

impl QueryBox {
    fn applied_to(
        &self,
        model: &Model,
        id_gen: &mut expr::IdGen,
        lowered_boxes: &mut HashMap<BoxId, expr::LocalId>,
        get_outer: expr::MirRelationExpr,
        outer_projection: &Vec<ColumnReference>,
    ) -> expr::MirRelationExpr {
        use expr::MirRelationExpr as SR;
        match &self.box_type {
            BoxType::BaseTable(_) => get_outer.product(SR::Get {
                // @todo get the global id from the metadata
                id: expr::Id::Global(expr::GlobalId::User(0)),
                typ: self.typ(model),
            }),
            BoxType::Select(select) => {
                let correlation_info = self.correlation_info(model);
                let (uncorrelated, correlated): (Vec<_>, Vec<_>) = correlation_info
                    .iter()
                    .partition(|(_q_id, outer_col_refs)| outer_col_refs.is_empty());

                if !correlated.is_empty() {
                    panic!("correlated queries are not yet supported");
                }

                let oa = outer_projection.len();
                let mut join_operands = Vec::new();
                let mut join_col_map = outer_projection.clone();
                let mut join_projection = (0..oa).collect::<Vec<_>>();
                for (i, (q_id, _)) in uncorrelated.iter().enumerate() {
                    let (join_operand, input_arity) =
                        model.get_quantifier(**q_id).borrow().applied_to(
                            model,
                            id_gen,
                            lowered_boxes,
                            get_outer.clone(),
                            outer_projection,
                        );
                    join_operands.push(join_operand);
                    join_projection.extend((0..input_arity).map(|c| oa * (i + 1) + c));
                    join_col_map.extend((0..input_arity).map(|position| ColumnReference {
                        quantifier_id: **q_id,
                        position,
                    }));
                }

                let mut product = if join_operands.len() == 1 {
                    join_operands[0].clone()
                } else {
                    SR::join(
                        join_operands,
                        (0..oa)
                            .map(|i| (0..uncorrelated.len()).map(|o| (o, i)).collect())
                            .collect(),
                    )
                };
                product = product
                    .project(join_projection)
                    // @todo do not produce empty filters
                    .filter(select.predicates.iter().map(|p| p.lower(&join_col_map)))
                    // @todo do not map column references
                    .map(
                        self.columns
                            .iter()
                            .map(|c| c.expr.lower(&join_col_map))
                            .collect(),
                    )
                    .project(
                        (join_col_map.len()..join_col_map.len() + self.columns.len()).collect(),
                    );

                // @todo correlated operands
                // @todo order by and limit

                if let DistinctOperation::Enforce = &self.distinct {
                    product = product.distinct();
                }

                product
            }
            _ => panic!(),
        }
    }

    fn typ(&self, _model: &Model) -> repr::RelationType {
        // @todo get the type information from the projection of the box
        repr::RelationType::new(
            (0..self.columns.len())
                .map(|_| repr::ColumnType {
                    nullable: true,
                    scalar_type: ScalarType::String,
                })
                .collect(),
        )
    }

    /// Correlation information of the quantifiers in this box
    fn correlation_info(&self, model: &Model) -> BTreeMap<QuantifierId, HashSet<ColumnReference>> {
        let mut correlation_info = BTreeMap::new();
        for q_id in self.quantifiers.iter() {
            let mut column_refs = HashSet::new();
            let mut f = |inner_box: &RefCell<QueryBox>| -> Result<(), ()> {
                inner_box
                    .borrow()
                    .visit_expressions(&mut |expr: &Expr| -> Result<(), ()> {
                        expr.collect_column_references_from_context(
                            &self.quantifiers,
                            &mut column_refs,
                        );
                        Ok(())
                    })
            };
            let q = model.get_quantifier(*q_id).borrow();
            model
                .visit_pre_boxes_in_subgraph(&mut f, q.input_box)
                .unwrap();
            correlation_info.insert(*q_id, column_refs);
        }
        correlation_info
    }
}

impl Quantifier {
    fn applied_to(
        &self,
        model: &Model,
        id_gen: &mut expr::IdGen,
        lowered_boxes: &mut HashMap<BoxId, expr::LocalId>,
        get_outer: expr::MirRelationExpr,
        outer_projection: &Vec<ColumnReference>,
    ) -> (expr::MirRelationExpr, usize) {
        assert!(matches!(self.quantifier_type, QuantifierType::Foreach));
        let input_box = model.get_box(self.input_box).borrow();
        let lowered_relation = if let Some(id) = lowered_boxes.get(&input_box.id) {
            expr::MirRelationExpr::Get {
                id: expr::Id::Local(id.clone()),
                typ: input_box.typ(model),
            }
        } else {
            let mut relation =
                input_box.applied_to(model, id_gen, lowered_boxes, get_outer, outer_projection);
            if input_box.ranging_quantifiers.len() > 1 {
                relation = relation.let_in(id_gen, |_id_gen, body| {
                    if let expr::MirRelationExpr::Get {
                        id: expr::Id::Local(local_id),
                        ..
                    } = &body
                    {
                        lowered_boxes.insert(input_box.id, local_id.clone());
                    }
                    body
                });
            }
            relation
        };
        (lowered_relation, input_box.columns.len())
    }
}

impl Expr {
    fn lower(&self, col_map: &Vec<ColumnReference>) -> expr::MirScalarExpr {
        match self {
            Expr::ColumnReference(c) => {
                if let Some(i) =
                    col_map
                        .iter()
                        .enumerate()
                        .find_map(|(i, col)| if c == col { Some(i) } else { None })
                {
                    expr::MirScalarExpr::column(i)
                } else {
                    panic!();
                }
            }
            _ => panic!(),
        }
    }
}
