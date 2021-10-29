// Copyright Materialize, Inc. and contributors. All rights reserved.
//
// Use of this software is governed by the Business Source License
// included in the LICENSE file.
//
// As of the Change Date specified in that file, in accordance with
// the Business Source License, use of this software will be governed
// by the Apache License, Version 2.0.

use crate::query_model::{
    BoxId, BoxType, DistinctOperation, Expr, Model, QuantifierId, QuantifierSet, QuantifierType,
    QueryBox,
};
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashSet};

#[allow(dead_code)]
pub enum RuleType {
    TopBoxOnly,
    PreOrder,
    PostOrder,
}

pub trait Rule {
    fn name(&self) -> &'static str;

    fn rule_type(&self) -> RuleType;

    /// Whether the action should be fired for the given box.
    /// This method is not allowed to modify the model in any way.
    fn condition(&mut self, model: &Model, box_id: BoxId) -> bool;

    /// Invoked immediately after `condition` if it returned true.
    fn action(&mut self, model: &mut Model, box_id: BoxId);
}

/// Entry-point of the normalization stage.
pub fn rewrite_model(model: &mut Model) {
    let mut rules: Vec<Box<dyn Rule>> = vec![
        Box::new(SelectMerge::new()),
        Box::new(ConstantLifting::new()),
        Box::new(OuterJoinNormalization::new()),
        Box::new(ColumnRemoval::new()),
    ];

    apply_rules_to_model(model, &mut rules);

    model.gargabe_collect();
}

/// Transform the model by applying a list of rewrite rules.
pub fn apply_rules_to_model(model: &mut Model, rules: &mut Vec<Box<dyn Rule>>) {
    for rule in rules
        .iter_mut()
        .filter(|r| matches!(r.rule_type(), RuleType::TopBoxOnly))
    {
        apply_rule(&mut **rule, model, model.top_box);
    }

    for _ in 0..5 {
        deep_apply_rules(rules, model, model.top_box, &mut HashSet::new());
    }
}

/// Apply a rewrite rule to a given box within the Model if it matches the condition.
fn apply_rule(rule: &mut dyn Rule, model: &mut Model, box_id: BoxId) {
    if rule.condition(model, box_id) {
        rule.action(model, box_id);
    }
}

/// Descend and apply recursively the given list of rewrite rules to all boxes within
/// the subgraph starting in the given box. `visited_boxes` keeps track of all the
/// visited boxes so far, to avoid visiting them again.
fn deep_apply_rules(
    rules: &mut Vec<Box<dyn Rule>>,
    model: &mut Model,
    box_id: BoxId,
    visited_boxes: &mut HashSet<BoxId>,
) {
    if visited_boxes.insert(box_id) {
        for rule in rules
            .iter_mut()
            .filter(|r| matches!(r.rule_type(), RuleType::PreOrder))
        {
            apply_rule(&mut **rule, model, box_id);
        }

        let quantifiers = model.get_box(box_id).borrow().quantifiers.clone();
        for q_id in quantifiers {
            let input_box = model.get_quantifier(q_id).borrow().input_box;
            deep_apply_rules(rules, model, input_box, visited_boxes);
        }

        for rule in rules
            .iter_mut()
            .filter(|r| matches!(r.rule_type(), RuleType::PostOrder))
        {
            apply_rule(&mut **rule, model, box_id);
        }
    }
}

/// Merges nested select boxes.
struct SelectMerge {
    to_merge: QuantifierSet,
}

impl SelectMerge {
    fn new() -> Self {
        Self {
            /// Set of quantifiers to be removed from the current box
            to_merge: BTreeSet::new(),
        }
    }
}

impl Rule for SelectMerge {
    fn name(&self) -> &'static str {
        "SelectMerge"
    }

    fn rule_type(&self) -> RuleType {
        RuleType::PostOrder
    }

    fn condition(&mut self, model: &Model, box_id: BoxId) -> bool {
        self.to_merge.clear();
        let outer_box = model.get_box(box_id).borrow();
        if let BoxType::Select(_outer_select) = &outer_box.box_type {
            for q_id in outer_box.quantifiers.iter() {
                let q = model.get_quantifier(*q_id).borrow();

                // Only Select boxes under Foreach quantifiers can be merged
                // into the parent Select box.
                if let QuantifierType::Foreach = q.quantifier_type {
                    let input_box = model.get_box(q.input_box).borrow();

                    // TODO(asenac) clone shared boxes
                    if input_box.ranging_quantifiers.len() == 1 {
                        if let BoxType::Select(inner_select) = &input_box.box_type {
                            if input_box.distinct != DistinctOperation::Enforce
                                && inner_select.order_key.is_none()
                                && inner_select.limit.is_none()
                            {
                                self.to_merge.insert(*q_id);
                            }
                        }
                    }
                }
            }
        }
        !self.to_merge.is_empty()
    }

    fn action(&mut self, model: &mut Model, box_id: BoxId) {
        // Dereference all the expressions in the sub-graph referencing the quantifiers
        // that are about to be squashed into the current box.
        let _ = model.visit_pre_boxes_in_subgraph(
            &mut |b: &RefCell<QueryBox>| -> Result<(), ()> {
                b.borrow_mut()
                    .visit_expressions_mut(&mut |expr: &mut Expr| -> Result<(), ()> {
                        expr.visit_mut(&mut |expr| {
                            if let Expr::ColumnReference(c) = expr {
                                if self.to_merge.contains(&c.quantifier_id) {
                                    let inner_box =
                                        model.get_quantifier(c.quantifier_id).borrow().input_box;
                                    let inner_box = model.get_box(inner_box).borrow();

                                    *expr = inner_box.columns[c.position].expr.clone();
                                }
                            }
                        });
                        Ok(())
                    })?;
                Ok(())
            },
            box_id,
        );

        // Add all the quantifiers in the input boxes of the quantifiers to be
        // merged into the current box
        let mut outer_box = model.get_box(box_id).borrow_mut();
        for q_id in self.to_merge.iter() {
            outer_box.quantifiers.remove(q_id);

            let input_box_id = model.get_quantifier(*q_id).borrow().input_box;
            let input_box = model.get_box(input_box_id).borrow();
            for child_q in input_box.quantifiers.iter() {
                model.get_quantifier(*child_q).borrow_mut().parent_box = box_id;
                outer_box.quantifiers.insert(*child_q);
            }
            if let Some(predicates) = input_box.get_predicates() {
                for p in predicates.iter() {
                    outer_box.add_predicate(p.clone());
                }
            }
        }
    }
}

/// Replaces any column reference pointing to a constant that can be lifted
/// with the constant value pointed.
///
/// Constants can only be lifted from Foreach quantifiers.
///
/// TODO(asenac) For unions, we can only lift a constant if all the branches
/// project the same constant in the same position.
struct ConstantLifting {}

impl ConstantLifting {
    fn new() -> Self {
        Self {}
    }
}

impl Rule for ConstantLifting {
    fn name(&self) -> &'static str {
        "ConstantLifting"
    }

    fn rule_type(&self) -> RuleType {
        RuleType::PostOrder
    }

    fn condition(&mut self, model: &Model, box_id: BoxId) -> bool {
        // No need to handle outer joins here since, once they are
        // normalized, their preserving quantifier is in a Select box.
        // TODO(asenac) grouping and unions
        model.get_box(box_id).borrow().is_select()
    }

    fn action(&mut self, model: &mut Model, box_id: BoxId) {
        let mut the_box = model.get_box(box_id).borrow_mut();

        // Dereference all column references and check whether the referenced
        // expression is constant within the context of the box it belongs to.
        let _ = the_box.visit_expressions_mut(&mut |e| -> Result<(), ()> {
            e.visit_mut(&mut |e| {
                if let Expr::ColumnReference(c) = e {
                    let q = model.get_quantifier(c.quantifier_id).borrow();
                    if let QuantifierType::Foreach = q.quantifier_type {
                        let input_box = model.get_box(q.input_box).borrow();
                        if input_box.columns[c.position]
                            .expr
                            .is_constant_within_context(&input_box.quantifiers)
                        {
                            *e = input_box.columns[c.position].expr.clone();
                        }
                    }
                }
            });
            Ok(())
        });
    }
}

struct OuterJoinNormalization {
    /// List with all the preserving quantifiers that can be lifted to the
    /// current box, with the child box they currently belong to.
    to_lift: Vec<(BoxId, QuantifierId)>,
}

impl OuterJoinNormalization {
    fn new() -> Self {
        Self {
            to_lift: Vec::new(),
        }
    }
}

impl Rule for OuterJoinNormalization {
    fn name(&self) -> &'static str {
        "OuterJoinNormalization"
    }

    fn rule_type(&self) -> RuleType {
        RuleType::PreOrder
    }

    fn condition(&mut self, model: &Model, box_id: BoxId) -> bool {
        self.to_lift.clear();
        let the_box = model.get_box(box_id).borrow();

        // Collect all preserving quantifiers from OuterJoin boxes hanging from
        // a Select box
        if the_box.is_select() {
            for q_id in the_box.quantifiers.iter() {
                let q = model.get_quantifier(*q_id).borrow();
                if let QuantifierType::Foreach = q.quantifier_type {
                    let input_box = model.get_box(q.input_box).borrow();
                    // TODO(asenac) clone shared sub-graphs
                    if input_box.ranging_quantifiers.len() == 1 {
                        if let BoxType::OuterJoin(_) = &input_box.box_type {
                            if let Some(preserving_q) = input_box.quantifiers.iter().find(|q| {
                                model.get_quantifier(**q).borrow().quantifier_type
                                    == QuantifierType::PreservedForeach
                            }) {
                                self.to_lift.push((input_box.id, *preserving_q));
                            }
                        }
                    }
                }
            }
        }
        !self.to_lift.is_empty()
    }

    fn action(&mut self, model: &mut Model, box_id: BoxId) {
        loop {
            let mut the_box = model.get_box(box_id).borrow_mut();
            for (child_box_id, preserving_q_id) in self.to_lift.iter() {
                let mut preserving_q = model.get_quantifier(*preserving_q_id).borrow_mut();

                // The preserving quantifier becomes a regular foreach quantifier
                // in the parent box
                preserving_q.quantifier_type = QuantifierType::Foreach;

                // Detach the quantifier from the child box
                let mut child_box = model.get_box(*child_box_id).borrow_mut();
                child_box.quantifiers.remove(preserving_q_id);

                // ... and attach it to the parent box
                preserving_q.parent_box = box_id;
                the_box.quantifiers.insert(*preserving_q_id);
            }
            // Release the borrow
            drop(the_box);

            // The quantifiers lifted may be pointing to outer join boxes
            // whose preserving quantifiers can be lifted as well.
            if !self.condition(model, box_id) {
                break;
            }
        }
    }
}

struct ColumnRemoval {
    new_projection: Option<BTreeMap<usize, usize>>,
}

impl ColumnRemoval {
    fn new() -> Self {
        Self {
            new_projection: None,
        }
    }
}

impl Rule for ColumnRemoval {
    fn name(&self) -> &'static str {
        "ColumnRemoval"
    }

    fn rule_type(&self) -> RuleType {
        RuleType::PreOrder
    }

    fn condition(&mut self, model: &Model, box_id: BoxId) -> bool {
        if model.top_box == box_id {
            false
        } else {
            let the_box = model.get_box(box_id).borrow();

            let mut column_positions = BTreeSet::new();

            for ranging_q_id in the_box.ranging_quantifiers.iter() {
                let mut column_refs = HashSet::new();
                let parent_box_id = model.get_quantifier(*ranging_q_id).borrow().parent_box;

                let q_id_as_set: BTreeSet<_> = std::iter::once(*ranging_q_id).collect();
                // TODO(asenac) avoid descending the ranging quantifier
                let _ = model.visit_pre_boxes_in_subgraph(
                    &mut |b| -> Result<(), ()> {
                        // TODO(asenac) special case for union. except, intersect
                        b.borrow().visit_expressions(&mut |e| -> Result<(), ()> {
                            e.collect_column_references_from_context(
                                &q_id_as_set,
                                &mut column_refs,
                            );
                            Ok(())
                        })
                    },
                    parent_box_id,
                );

                column_positions.extend(column_refs.iter().map(|c| c.position));
            }

            if column_positions.len() != the_box.columns.len() {
                let new_projection = column_positions
                    .iter()
                    .enumerate()
                    .map(|(i, c)| (*c, i))
                    .collect();
                self.new_projection = Some(new_projection);
            } else {
                self.new_projection = None;
            }

            self.new_projection.is_some()
        }
    }

    fn action(&mut self, model: &mut Model, box_id: BoxId) {
        let new_projection = self.new_projection.as_ref().unwrap();
        let mut the_box = model.get_box(box_id).borrow_mut();
        the_box.columns = new_projection
            .iter()
            .map(|(c, _)| the_box.columns[*c].clone())
            .collect();
        drop(the_box);

        let ranging_quantifiers = model.get_box(box_id).borrow().ranging_quantifiers.clone();
        for ranging_q_id in ranging_quantifiers.iter() {
            let parent_box_id = model.get_quantifier(*ranging_q_id).borrow().parent_box;

            let _ = model.visit_pre_boxes_in_subgraph(
                &mut |b| -> Result<(), ()> {
                    b.borrow_mut()
                        .visit_expressions_mut(&mut |e| -> Result<(), ()> {
                            e.visit_mut(&mut |e| {
                                if let Expr::ColumnReference(c) = e {
                                    if c.quantifier_id == *ranging_q_id {
                                        c.position = new_projection[&c.position];
                                    }
                                }
                            });
                            Ok(())
                        })
                },
                parent_box_id,
            );
        }
    }
}
