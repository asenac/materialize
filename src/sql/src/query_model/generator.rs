// Copyright Materialize, Inc. and contributors. All rights reserved.
//
// Use of this software is governed by the Business Source License
// included in the LICENSE file.
//
// As of the Change Date specified in that file, in accordance with
// the Business Source License, use of this software will be governed
// by the Apache License, Version 2.0.

use crate::query_model::{
    BaseColumn, BaseTable, BoxId, BoxType, Column, ColumnReference, DistinctOperation, Expr,
    Grouping, Model, OuterJoin, QuantifierId, QuantifierType, Select, Values,
};
use anyhow::bail;
use sql_parser::ast::{
    Cte, Ident, Query, Raw, SelectStatement, SetExpr, TableFactor, TableWithJoins,
};
use sql_parser::ast::{JoinConstraint, TableAlias};
use std::collections::HashMap;

pub(crate) struct ModelGenerator {}

impl ModelGenerator {
    pub fn new() -> Self {
        Self {}
    }

    pub fn generate(self, statement: &SelectStatement<Raw>) -> Result<Model, anyhow::Error> {
        let mut model = Model::new();
        {
            let generator = ModelGeneratorImpl::new(&mut model);
            generator.process_top_level_query(&statement.query)?;
        }
        Ok(model)
    }
}

struct ModelGeneratorImpl<'a> {
    model: &'a mut Model,
}

impl<'a> ModelGeneratorImpl<'a> {
    fn new(model: &'a mut Model) -> Self {
        Self { model }
    }

    fn process_top_level_query(mut self, query: &Query<Raw>) -> Result<(), anyhow::Error> {
        let top_box = self.process_query(query, None)?;
        self.model.top_box = top_box;
        Ok(())
    }

    fn process_query(
        &mut self,
        query: &Query<Raw>,
        parent_context: Option<&NameResolutionContext>,
    ) -> Result<BoxId, anyhow::Error> {
        let box_id = self.model.make_select_box();
        let mut current_context = NameResolutionContext::new(box_id, parent_context);
        self.add_ctes_to_context(&query.ctes, &mut current_context)?;
        self.process_query_body(&query.body, box_id, &mut current_context)?;
        // @todo limit, offset

        // the projection of the box can be used for name resolution
        current_context.enable_box_projection();

        if !query.order_by.is_empty() {
            let mut key = Vec::new();
            for key_item in query.order_by.iter() {
                // @todo direction
                let expr = self.process_expr(&key_item.expr, &current_context, Some(box_id))?;
                key.push(Box::new(expr));
            }

            let mut select_box = self.model.get_box(box_id).borrow_mut();
            if let BoxType::Select(select) = &mut select_box.box_type {
                select.order_key = Some(key);
            } else {
                panic!();
            }
        }
        Ok(box_id)
    }

    fn add_ctes_to_context(
        &mut self,
        ctes: &Vec<Cte<Raw>>,
        context: &mut NameResolutionContext,
    ) -> Result<(), anyhow::Error> {
        // @todo CTEs can see previous CTEs within the same list
        for cte in ctes.iter() {
            let mut cte_id = self.process_query(&cte.query, context.parent_context.clone())?;
            cte_id = self.add_column_aliases(cte_id, &cte.alias.columns);
            context.ctes.insert(cte.alias.name.clone(), cte_id);
        }
        Ok(())
    }

    /// Fills the given select box with the body.
    fn process_query_body(
        &mut self,
        body: &SetExpr<Raw>,
        query_box: BoxId,
        context: &mut NameResolutionContext,
    ) -> Result<(), anyhow::Error> {
        match body {
            SetExpr::Select(select) => self.process_select(&*select, query_box, context),
            SetExpr::Values(values) => self.process_values(&*values, query_box, context),
            SetExpr::Query(query) => {
                let box_id = self.process_query(&*query, Some(context))?;
                let _ = self
                    .model
                    .make_quantifier(QuantifierType::Foreach, box_id, query_box);
                self.model
                    .get_box(query_box)
                    .borrow_mut()
                    .add_all_input_columns(self.model);
                Ok(())
            }
            SetExpr::SetOperation {
                op,
                all,
                left,
                right,
            } => {
                let box_type = match op {
                    sql_parser::ast::SetOperator::Union => BoxType::Union,
                    sql_parser::ast::SetOperator::Intersect => BoxType::Intersect,
                    sql_parser::ast::SetOperator::Except => BoxType::Except,
                };
                let box_id = self.model.make_box(box_type);
                let _left_box = {
                    let left_box = self.model.make_select_box();
                    let mut child_context =
                        NameResolutionContext::new(left_box, context.parent_context);
                    self.process_query_body(&**left, left_box, &mut child_context)?;
                    let left_q_id =
                        self.model
                            .make_quantifier(QuantifierType::Foreach, left_box, box_id);

                    // project all the columns from the left side
                    let b_left_box = self.model.get_box(left_box).borrow();
                    let mut set_box = self.model.get_box(box_id).borrow_mut();
                    for (position, c) in b_left_box.columns.iter().enumerate() {
                        let expr = Expr::ColumnReference(ColumnReference {
                            quantifier_id: left_q_id,
                            position,
                        });
                        set_box.columns.push(Column {
                            expr,
                            alias: c.alias.clone(),
                        });
                    }
                    left_box
                };

                let _right_box = {
                    let right_box = self.model.make_select_box();
                    let mut child_context =
                        NameResolutionContext::new(right_box, context.parent_context);
                    self.process_query_body(&**right, right_box, &mut child_context)?;
                    let _ = self
                        .model
                        .make_quantifier(QuantifierType::Foreach, right_box, box_id);
                    right_box
                };

                if !*all {
                    self.model.get_box(box_id).borrow_mut().distinct = DistinctOperation::Enforce;
                }

                let _ = self
                    .model
                    .make_quantifier(QuantifierType::Foreach, box_id, query_box);
                self.model
                    .get_box(query_box)
                    .borrow_mut()
                    .add_all_input_columns(self.model);
                Ok(())
            }
        }
    }

    fn process_select(
        &mut self,
        select: &sql_parser::ast::Select<Raw>,
        query_box: BoxId,
        context: &mut NameResolutionContext,
    ) -> Result<(), anyhow::Error> {
        // @todo collect aggregates
        let is_grouping = !select.group_by.is_empty() || select.having.is_some();

        let (join_box, mut join_context) = if is_grouping {
            let join_box = self.model.make_select_box();
            (
                join_box,
                NameResolutionContext::new(join_box, context.parent_context.clone()),
            )
        } else {
            (query_box, context.clone())
        };

        self.process_from_clause(&select.from, join_box, &mut join_context)?;

        if let Some(selection) = &select.selection {
            let predicate = self.process_expr(&selection, &join_context, Some(join_box))?;
            self.model
                .get_box(join_box)
                .borrow_mut()
                .add_predicate(Box::new(predicate));
        }

        if is_grouping {
            let mut grouping_key = Vec::new();
            for key_item in select.group_by.iter() {
                let key_item = self.process_expr(&key_item, &join_context, Some(join_box))?;
                let alias = self.get_expression_alias(&key_item);
                // ensure the key is projected by the input box of the grouping
                let key_position = self
                    .model
                    .get_box(join_box)
                    .borrow_mut()
                    .add_column_if_not_exists(key_item, alias);
                grouping_key.push(key_position);
            }

            // Note: the grouping box is created temporarily as a select box so
            // that we can create the input quantifier that is referenced by
            // the grouping key
            let grouping_box = self.model.make_select_box();
            let quantifier_id =
                self.model
                    .make_quantifier(QuantifierType::Foreach, join_box, grouping_box);

            let grouping_key = grouping_key
                .iter()
                .map(|position| {
                    Box::new(Expr::ColumnReference(ColumnReference {
                        quantifier_id,
                        position: *position,
                    }))
                })
                .collect::<Vec<_>>();

            {
                let mut grouping_box = self.model.get_box(grouping_box).borrow_mut();

                // add all the columns in the grouping key to the projection of the
                // grouping box
                for key_item in grouping_key.iter() {
                    grouping_box.columns.push(Column {
                        expr: (**key_item).clone(),
                        alias: self.get_expression_alias(&**key_item),
                    });
                }

                // @todo add all the columns from the join_box that functionally depend on
                // the columns in the grouping key to the projection of the grouping_box
                grouping_box.box_type = BoxType::Grouping(Grouping { key: grouping_key });

                // any expression on top of a grouping box must be liftable through
                // its projection
                context.grouping_box = Some(grouping_box.id);
            }

            // make the grouping box the input of the parent select box
            let _ = self
                .model
                .make_quantifier(QuantifierType::Foreach, grouping_box, query_box);
        }

        let base_quantifiers = join_context.disown_quantifiers();
        context.merge_quantifiers(base_quantifiers);

        if let Some(having) = &select.having {
            let predicate = self.process_expr(having, context, Some(query_box))?;
            self.model
                .get_box(query_box)
                .borrow_mut()
                .add_predicate(Box::new(predicate));
        }

        self.process_projection(&select.projection, query_box, context)?;

        if let Some(distinct) = &select.distinct {
            match distinct {
                sql_parser::ast::Distinct::EntireRow => {
                    self.model.get_box(query_box).borrow_mut().distinct =
                        DistinctOperation::Enforce;
                }
                _ => bail!("@todo unsupported stuff"),
            }
        }
        Ok(())
    }

    fn process_projection(
        &mut self,
        projection: &Vec<sql_parser::ast::SelectItem<Raw>>,
        query_box: BoxId,
        context: &mut NameResolutionContext,
    ) -> Result<(), anyhow::Error> {
        use sql_parser::ast;

        // Add all columns projected by the given quantifier to the projection
        // of the current box. Returns an error in any column is not liftable
        // all the way up to the owner box of the context of the quantifier.
        let add_all_columns_to_projection = |model: &Model,
                                             quantifier_context: &NameResolutionContext,
                                             quantifier_id: QuantifierId|
         -> Result<(), anyhow::Error> {
            let q = model.get_quantifier(quantifier_id);
            let bq = q.borrow();
            let input_box = model.get_box(bq.input_box).borrow();
            for (position, c) in input_box.columns.iter().enumerate() {
                let expr = Expr::ColumnReference(ColumnReference {
                    quantifier_id,
                    position,
                });
                let expr = quantifier_context.pullup_column_reference(model, expr)?;
                let expr = quantifier_context.pullup_expression_through_group_by(model, expr)?;
                model.get_box(query_box).borrow_mut().columns.push(Column {
                    expr,
                    alias: c.alias.clone(),
                });
            }
            Ok(())
        };

        for si in projection {
            match si {
                ast::SelectItem::Wildcard => {
                    for quantifier_id in context.quantifiers.iter() {
                        add_all_columns_to_projection(self.model, context, *quantifier_id)?;
                    }
                }
                ast::SelectItem::Expr {
                    expr: ast::Expr::QualifiedWildcard(table_name),
                    alias: _,
                } => {
                    // @todo qualified tables
                    if let Some((context, quantifier_id)) =
                        context.resolve_quantifier(self.model, table_name.last().unwrap())
                    {
                        add_all_columns_to_projection(self.model, context, quantifier_id)?;
                    } else {
                        bail!("unknown table {:?}", table_name);
                    }
                }
                ast::SelectItem::Expr { expr, alias } => {
                    let expr = self.process_expr(expr, context, Some(query_box))?;
                    let alias = if let Some(alias) = alias {
                        Some(alias.clone())
                    } else {
                        self.get_expression_alias(&expr)
                    };
                    self.model
                        .get_box(query_box)
                        .borrow_mut()
                        .columns
                        .push(Column { expr, alias });
                }
            }
        }
        Ok(())
    }

    /// Process the FROM clause of a Select represented by the given `query_box`.
    /// `context` is the empty name resolution context that will be used for name
    /// resolution of expressions within the given `query_box`, and that is fully
    /// populated after this method.
    fn process_from_clause(
        &mut self,
        from: &Vec<TableWithJoins<Raw>>,
        query_box: BoxId,
        context: &mut NameResolutionContext,
    ) -> Result<(), anyhow::Error> {
        if from.is_empty() {
            let values_id = self
                .model
                .make_box(BoxType::Values(Values { rows: vec![vec![]] }));
            let _ = self
                .model
                .make_quantifier(QuantifierType::Foreach, values_id, query_box);
        } else {
            for twj in from.iter() {
                self.process_comma_join_operand(&twj, context)?;
            }
        }
        Ok(())
    }

    /// Process comma-join operands and nested joins. Returns the box id of the
    /// box representing the join.
    fn process_comma_join_operand(
        &mut self,
        twj: &TableWithJoins<Raw>,
        context: &mut NameResolutionContext,
    ) -> Result<(), anyhow::Error> {
        // all comma-join operands are foreach quantifier
        let _ =
            self.process_join_tree(&twj.relation, &twj.joins, QuantifierType::Foreach, context)?;
        Ok(())
    }

    fn process_join_tree(
        &mut self,
        leftmost_relation: &TableFactor<Raw>,
        joins: &[sql_parser::ast::Join<Raw>],
        quantifier_type: QuantifierType,
        context: &mut NameResolutionContext,
    ) -> Result<QuantifierId, anyhow::Error> {
        if let Some(join) = joins.last() {
            let (box_type, left_q_type, right_q_type) = match &join.join_operator {
                sql_parser::ast::JoinOperator::CrossJoin
                | sql_parser::ast::JoinOperator::Inner(_) => (
                    BoxType::Select(Select::new()),
                    QuantifierType::Foreach,
                    QuantifierType::Foreach,
                ),
                sql_parser::ast::JoinOperator::FullOuter(_) => (
                    BoxType::OuterJoin(OuterJoin::new()),
                    QuantifierType::PreservedForeach,
                    QuantifierType::PreservedForeach,
                ),
                sql_parser::ast::JoinOperator::LeftOuter(_) => (
                    BoxType::OuterJoin(OuterJoin::new()),
                    QuantifierType::PreservedForeach,
                    QuantifierType::Foreach,
                ),
                sql_parser::ast::JoinOperator::RightOuter(_) => (
                    BoxType::OuterJoin(OuterJoin::new()),
                    QuantifierType::Foreach,
                    QuantifierType::PreservedForeach,
                ),
            };
            let join_id = self.model.make_box(box_type);

            let mut join_context = NameResolutionContext::for_join(join_id, context);

            // keep processing the join tree recursively
            let _left_q = self.process_join_tree(
                leftmost_relation,
                &joins[..joins.len() - 1],
                left_q_type,
                &mut join_context,
            )?;
            let _right_q =
                self.process_table_factor(&join.relation, right_q_type, &mut join_context)?;

            match &join.join_operator {
                sql_parser::ast::JoinOperator::CrossJoin => {
                    let join = self.model.get_box(join_id);
                    join.borrow_mut().add_all_input_columns(self.model);
                }
                sql_parser::ast::JoinOperator::Inner(constraint)
                | sql_parser::ast::JoinOperator::FullOuter(constraint)
                | sql_parser::ast::JoinOperator::LeftOuter(constraint)
                | sql_parser::ast::JoinOperator::RightOuter(constraint) => {
                    self.process_join_constraint(constraint, join_id, &mut join_context)?;
                }
            }

            let child_quantifiers = join_context.disown_quantifiers();
            context.merge_quantifiers(child_quantifiers);

            // add the join as a quantifier in the parent join
            let quantifier_id =
                self.model
                    .make_quantifier(quantifier_type, join_id, context.owner_box);

            Ok(quantifier_id)
        } else {
            self.process_table_factor(leftmost_relation, quantifier_type, context)
        }
    }

    fn process_table_factor(
        &mut self,
        table_factor: &TableFactor<Raw>,
        quantifier_type: QuantifierType,
        context: &mut NameResolutionContext,
    ) -> Result<QuantifierId, anyhow::Error> {
        let (mut box_id, is_scope, alias) = match table_factor {
            TableFactor::Table { name, alias } => {
                let alias = if let Some(_) = alias {
                    alias.clone()
                } else {
                    let name = self.extract_name(name)?;
                    Some(TableAlias {
                        name,
                        columns: Vec::new(),
                        strict: false,
                    })
                };
                if let Some(cte_id) = context.resolve_cte(&self.extract_name(name)?) {
                    (cte_id, true, alias.clone())
                } else {
                    // @todo resolve them from the catalog and cache them
                    let box_id = self.model.make_box(BoxType::BaseTable(BaseTable::new()));
                    let mut base_table = self.model.get_box(box_id).borrow_mut();
                    for i in 0..3 {
                        base_table.columns.push(Column {
                            expr: Expr::BaseColumn(BaseColumn { position: i }),
                            alias: Some(Ident::new(format!("column{}", i + 1))),
                        });
                    }
                    (box_id, true, alias.clone())
                }
            }
            TableFactor::NestedJoin { join, alias } => {
                let join_id = self.model.make_select_box();
                let mut join_context = NameResolutionContext::for_join(join_id, context);

                self.process_comma_join_operand(join, &mut join_context)?;

                // if the nested join doesn't have an alias, its base tables are
                // visible from the parent join scope
                if alias.is_none() {
                    let child_quantifiers = join_context.disown_quantifiers();
                    context.merge_quantifiers(child_quantifiers);
                }

                // project everything
                self.model
                    .get_box(join_id)
                    .borrow_mut()
                    .add_all_input_columns(self.model);

                (join_id, alias.is_some(), alias.clone())
            }
            TableFactor::Derived {
                lateral,
                subquery,
                alias,
            } => {
                // For lateral join operands, the current context is put in
                // lateral mode and passed as the parent context of the
                // derived relation.
                let box_id = if *lateral {
                    let lateral_context = context.enable_lateral();
                    self.process_query(&subquery, Some(&lateral_context))?
                } else {
                    self.process_query(&subquery, context.parent_context.clone())?
                };

                (box_id, true, alias.clone())
            }
            _ => bail!("unsupported stuff"),
        };

        if let Some(alias) = &alias {
            if alias.strict
                && alias.columns.len() != self.model.get_box(box_id).borrow().columns.len()
            {
                bail!("column number mismatch");
            }
            // add intermediate select box with the column aliases
            box_id = self.add_column_aliases(box_id, &alias.columns);
        }

        // Add the box to the current join with the given type
        let quantifier_id = self
            .model
            .make_quantifier(quantifier_type, box_id, context.owner_box);

        if let Some(alias) = &alias {
            self.model.get_quantifier(quantifier_id).borrow_mut().alias = Some(alias.name.clone());
        }

        if is_scope {
            context.quantifiers.push(quantifier_id);
        }
        Ok(quantifier_id)
    }

    /// Add the join constraint to the given join box and populates the projection
    /// of the box accordingly: ON-joins propagate all columns from all input quantifiers
    /// while USING/NATURAL-joins propagate first joined columns and then the rest.
    fn process_join_constraint(
        &mut self,
        constraint: &JoinConstraint<Raw>,
        join_id: BoxId,
        context: &mut NameResolutionContext,
    ) -> Result<(), anyhow::Error> {
        match constraint {
            JoinConstraint::On(expr) => {
                let expr = self.process_expr(expr, context, Some(join_id))?;
                let join = self.model.get_box(join_id);
                let mut mut_join = join.borrow_mut();
                mut_join.add_predicate(Box::new(expr));
                mut_join.add_all_input_columns(self.model);
            }
            _ => bail!("unsupported stuff"),
        }
        Ok(())
    }

    fn process_values(
        &mut self,
        values: &sql_parser::ast::Values<Raw>,
        query_box: BoxId,
        context: &mut NameResolutionContext,
    ) -> Result<(), anyhow::Error> {
        let mut rows = Vec::with_capacity(values.0.len());
        for values in values.0.iter() {
            let mut row = Vec::with_capacity(values.len());
            for value in values.iter() {
                let expr = self.process_expr(value, context, Some(query_box))?;
                row.push(Box::new(expr));
            }
            rows.push(row);
        }
        let num_rows = rows.iter().next().map_or(0, |x| x.len());
        let values_id = self.model.make_box(BoxType::Values(Values { rows }));
        let quantifier_id =
            self.model
                .make_quantifier(QuantifierType::Foreach, values_id, query_box);
        let mut query_box = self.model.get_box(query_box).borrow_mut();
        let mut values_box = self.model.get_box(values_id).borrow_mut();
        for i in 0..num_rows {
            let ident = Ident::new(format!("column{}", i + 1));
            query_box.columns.push(Column {
                expr: Expr::ColumnReference(ColumnReference {
                    quantifier_id,
                    position: i,
                }),
                alias: Some(ident.clone()),
            });
            values_box.columns.push(Column {
                expr: Expr::BaseColumn(BaseColumn { position: i }),
                alias: Some(ident.clone()),
            });
        }
        Ok(())
    }

    fn process_expr(
        &mut self,
        expr: &sql_parser::ast::Expr<Raw>,
        context: &NameResolutionContext,
        join_id: Option<BoxId>,
    ) -> Result<Expr, anyhow::Error> {
        let expr = self.process_expr_impl(expr, context, join_id)?;

        // Try to lift the expression through the projection of the
        // grouping box, if set.
        context.pullup_expression_through_group_by(self.model, expr)
    }

    fn process_expr_impl(
        &mut self,
        expr: &sql_parser::ast::Expr<Raw>,
        context: &NameResolutionContext,
        join_id: Option<BoxId>,
    ) -> Result<Expr, anyhow::Error> {
        use sql_parser::ast;
        let expr = match expr {
            ast::Expr::Identifier(id) => self.process_identifier(id, context)?,
            ast::Expr::Subquery(query) => {
                let quantifier_id =
                    self.process_subquery(query, context, &join_id, QuantifierType::Scalar)?;
                // @todo multi-column scalar subqueries
                Expr::ColumnReference(ColumnReference {
                    quantifier_id,
                    position: 0,
                })
            }
            _ => bail!("unsupported stuff"),
        };

        Ok(expr)
    }

    fn process_identifier(
        &mut self,
        id: &Vec<Ident>,
        context: &NameResolutionContext,
    ) -> Result<Expr, anyhow::Error> {
        context.resolve_column(&self.model, id)
    }

    /// Add a subquery quantifier of the given type to the given join box ranging over
    /// the box resulting of processing the given query tree.
    ///
    /// Return the resulting quantifier.
    fn process_subquery(
        &mut self,
        query: &sql_parser::ast::Query<Raw>,
        context: &NameResolutionContext,
        join_id: &Option<BoxId>,
        quantifier_type: QuantifierType,
    ) -> Result<QuantifierId, anyhow::Error> {
        if let Some(join_id) = join_id {
            let subquery_box = self.process_query(query, Some(context))?;
            Ok(self
                .model
                .make_quantifier(quantifier_type, subquery_box, *join_id))
        } else {
            // @todo what context?
            bail!("subqueries are not supported within this context")
        }
    }

    /// Add an intermediate select box on top of the given input box for applying
    /// the given column aliases
    fn add_column_aliases(&mut self, input_box: BoxId, columns: &Vec<Ident>) -> BoxId {
        if !columns.is_empty() {
            let select_id = self.model.make_select_box();
            let quantifier_id =
                self.model
                    .make_quantifier(QuantifierType::Foreach, input_box, select_id);
            let mut select = self.model.get_box(select_id).borrow_mut();
            for (position, c) in columns.iter().enumerate() {
                select.columns.push(Column {
                    expr: Expr::ColumnReference(ColumnReference {
                        quantifier_id,
                        position,
                    }),
                    alias: Some(c.clone()),
                });
            }
            select_id
        } else {
            input_box
        }
    }

    /// @todo support for RawName::Id
    fn extract_name(&self, name: &sql_parser::ast::RawName) -> Result<Ident, anyhow::Error> {
        let name = match name {
            sql_parser::ast::RawName::Name(c) => c.0.last().cloned().unwrap(),
            _ => bail!("unsupported"),
        };
        Ok(name)
    }

    fn get_expression_alias(&self, expr: &Expr) -> Option<Ident> {
        if let Expr::ColumnReference(c) = expr {
            self.get_column_alias(c.quantifier_id, c.position)
        } else {
            None
        }
    }

    /// Return the column alias/name of the column projected in the given position
    /// by the input box of the given quantifier
    fn get_column_alias(&self, quantifier_id: QuantifierId, position: usize) -> Option<Ident> {
        let q = self.model.get_quantifier(quantifier_id).borrow();
        let ib = self.model.get_box(q.input_box).borrow();
        ib.columns[position].alias.clone()
    }
}

#[derive(Clone)]
struct NameResolutionContext<'a> {
    owner_box: BoxId,
    /// leaf quantifiers for resolving column names
    quantifiers: Vec<QuantifierId>,
    /// the size of the default projections of the intermediate boxes from
    /// the leaf quantifiers up to the owner_box/grouping_box.
    default_projections: HashMap<BoxId, usize>,
    grouping_box: Option<BoxId>,
    /// CTEs visibile within this context
    ctes: HashMap<Ident, BoxId>,
    /// an optional parent context
    parent_context: Option<&'a NameResolutionContext<'a>>,
    /// the sibling context: only visible if `is_lateral` is true
    sibling_context: Option<&'a NameResolutionContext<'a>>,
    /// enables/disables the visibility of the sibling scope
    is_lateral: bool,
    /// Whether the projection of the owner box must be used for resolving unqualified
    /// column names.
    ///
    /// This exists to support the special behavior of scoping in intrusive
    /// `ORDER BY` clauses. For example, in the following `SELECT` statement
    ///
    ///   CREATE TABLE t (a int, b)
    ///   SELECT 'outer' AS a, b FROM t ORDER BY a
    ///
    /// even though there are two columns named `a` in scope in the ORDER BY
    /// (one from `t` and one declared in the select list), the column declared
    /// in the select list has priority. Remember that if there are two columns
    /// named `a` that are both in the priority class, as in
    ///
    ///   SELECT 'outer' AS a, a FROM t ORDER BY a
    ///
    /// this still needs to generate an "ambiguous name" error.
    use_box_projection: bool,
}

impl<'a> NameResolutionContext<'a> {
    fn new(owner_box: BoxId, parent_context: Option<&'a NameResolutionContext<'a>>) -> Self {
        Self {
            owner_box,
            quantifiers: Vec::new(),
            default_projections: HashMap::new(),
            grouping_box: None,
            ctes: HashMap::new(),
            parent_context,
            sibling_context: None,
            is_lateral: false,
            use_box_projection: false,
        }
    }

    /// Creates a new context for an intermediate join.
    fn for_join(join_box: BoxId, sibling_context: &'a NameResolutionContext<'a>) -> Self {
        Self {
            owner_box: join_box,
            quantifiers: Vec::new(),
            default_projections: HashMap::new(),
            grouping_box: None,
            ctes: HashMap::new(),
            parent_context: sibling_context.parent_context.clone(),
            sibling_context: Some(sibling_context),
            is_lateral: false,
            use_box_projection: false,
        }
    }

    /// Clones the current context, with lateral name resolution enabled
    fn enable_lateral(&self) -> Self {
        let mut clone = self.clone();
        clone.is_lateral = true;
        clone
    }

    /// Makes the projection of the box visible for name resolution.
    fn enable_box_projection(&mut self) {
        self.use_box_projection = true;
    }

    fn disown_quantifiers(self) -> (Vec<QuantifierId>, HashMap<BoxId, usize>) {
        (self.quantifiers, self.default_projections)
    }

    fn merge_quantifiers(&mut self, quantifiers: (Vec<QuantifierId>, HashMap<BoxId, usize>)) {
        self.quantifiers.extend(quantifiers.0);
        self.default_projections.extend(quantifiers.1);
    }

    fn resolve_cte(&self, name: &Ident) -> Option<BoxId> {
        if let Some(id) = self.ctes.get(name) {
            return Some(*id);
        }
        if let Some(parent_context) = &self.parent_context {
            return parent_context.resolve_cte(name);
        }
        None
    }

    fn resolve_column(&self, model: &Model, name: &Vec<Ident>) -> Result<Expr, anyhow::Error> {
        let mut current_ctx = Some(self);

        while let Some(current) = current_ctx {
            if let Some(expr) = current.resolve_column_in_context(model, name)? {
                return Ok(expr);
            }

            if current.is_lateral {
                // move laterally first
                let mut sibling_ctx = current.sibling_context.clone();
                while let Some(sibling) = sibling_ctx {
                    if let Some(expr) = sibling.resolve_column_in_context(model, name)? {
                        return Ok(expr);
                    }
                    sibling_ctx = sibling.sibling_context.clone();
                }
            }

            current_ctx = current.parent_context.clone();
        }

        bail!("column {:?} could not be resolved", name)
    }

    /// Resolve the column identified by name against the quantifiers in this context.
    /// Returns a column reference expression if found. Checks whether the column name
    /// is ambiguous within the current context.
    fn resolve_column_in_context(
        &self,
        model: &Model,
        name: &Vec<Ident>,
    ) -> Result<Option<Expr>, anyhow::Error> {
        let expr = match name.len() {
            1 => {
                let mut found = None;
                for quantifier_id in self.quantifiers.iter() {
                    if let Some(expr) =
                        self.resolve_column_in_quantifier(model, *quantifier_id, &name[0])?
                    {
                        if found.is_some() {
                            bail!("ambiguous column name {:?}", name);
                        }
                        found = Some(expr);
                    }
                }

                if self.use_box_projection {
                    let owner_box = model.get_box(self.owner_box).borrow();
                    for c in owner_box.columns.iter() {
                        if let Some(alias) = &c.alias {
                            if *alias == name[0] {
                                if let Some(found) = &found {
                                    if *found != c.expr {
                                        bail!("ambiguous column name {:?}", name);
                                    }
                                } else {
                                    found = Some(c.expr.clone());
                                }
                            }
                        }
                    }
                }

                found
            }
            2 => {
                if let Some(quantifier_id) = self.resolve_quantifier_in_context(model, &name[0]) {
                    self.resolve_column_in_quantifier(model, quantifier_id, &name[1])?
                } else {
                    None
                }
            }
            _ => bail!("unsupported stuff"),
        };

        Ok(expr)
    }

    /// Checks whether the column name is ambiguous within the current quantifier. Note:
    /// a derived relation could expose several columns with the same alias.
    fn resolve_column_in_quantifier(
        &self,
        model: &Model,
        quantifier_id: QuantifierId,
        name: &Ident,
    ) -> Result<Option<Expr>, anyhow::Error> {
        let q = model.get_quantifier(quantifier_id).borrow();
        let input_box = model.get_box(q.input_box).borrow();
        let mut found = None;
        for (position, c) in input_box.columns.iter().enumerate() {
            if let Some(alias) = &c.alias {
                if alias == name {
                    if found.is_some() {
                        bail!("ambiguous column name {}", name);
                    }

                    found = Some(position);
                }
            }
        }

        if let Some(position) = found {
            let expr = Expr::ColumnReference(ColumnReference {
                quantifier_id,
                position,
            });
            let expr = self.pullup_column_reference(model, expr)?;
            Ok(Some(expr))
        } else {
            Ok(None)
        }
    }

    /// @todo support qualified quantifiers
    fn resolve_quantifier_in_context(&self, model: &Model, name: &Ident) -> Option<QuantifierId> {
        for q_id in self.quantifiers.iter() {
            let q = model.get_quantifier(*q_id).borrow();
            if let Some(alias) = &q.alias {
                if alias == name {
                    return Some(*q_id);
                }
            }
        }

        None
    }

    /// @todo support qualified quantifiers
    fn resolve_quantifier(
        &'a self,
        model: &Model,
        name: &Ident,
    ) -> Option<(&'a NameResolutionContext<'a>, QuantifierId)> {
        let mut current_ctx = Some(self);

        while let Some(current) = current_ctx {
            if let Some(q_id) = current.resolve_quantifier_in_context(model, name) {
                return Some((current, q_id));
            }

            if current.is_lateral {
                // move laterally first
                let mut sibling_ctx = current.sibling_context.clone();
                while let Some(sibling) = sibling_ctx {
                    if let Some(q_id) = sibling.resolve_quantifier_in_context(model, name) {
                        return Some((sibling, q_id));
                    }
                    sibling_ctx = sibling.sibling_context.clone();
                }
            }
            current_ctx = current.parent_context.clone();
        }

        None
    }

    /// Given a column reference expression, returns another column reference
    /// expression that points to one of the quantifiers in the owner box of
    /// this context or in the grouping box, if set.
    /// Adds the given column to the projection of all the intermediate boxes.
    fn pullup_column_reference(&self, model: &Model, expr: Expr) -> Result<Expr, anyhow::Error> {
        match expr {
            Expr::ColumnReference(mut c) => {
                loop {
                    let q = model.get_quantifier(c.quantifier_id).borrow();
                    if q.parent_box == self.owner_box
                        || self
                            .grouping_box
                            .map_or(false, |grouping_box| q.parent_box == grouping_box)
                    {
                        // We have reached a quantifier within either the owner box
                        // or the grouping box. Expressions are lifted through
                        // the projection of the grouping box through
                        // `pullup_expression_through_group_by`.
                        break;
                    }
                    let alias = {
                        let b = model.get_box(q.input_box).borrow();
                        b.columns[c.position].alias.clone()
                    };
                    let mut parent_box = model.get_box(q.parent_box).borrow_mut();
                    assert!(parent_box.ranging_quantifiers.len() == 1);
                    let parent_q_id = *parent_box.ranging_quantifiers.iter().next().unwrap();
                    match &parent_box.box_type {
                        BoxType::Select(_) | BoxType::OuterJoin(_) => {
                            let expr = Expr::ColumnReference(c.clone());
                            c.position = parent_box.add_column_if_not_exists(expr, alias)
                        }
                        _ => panic!("unexpected box type"),
                    }
                    c.quantifier_id = parent_q_id;
                }
                Ok(Expr::ColumnReference(c.clone()))
            }
            _ => panic!("expected column reference"),
        }
    }

    fn pullup_expression_through_group_by(
        &self,
        model: &Model,
        expr: Expr,
    ) -> Result<Expr, anyhow::Error> {
        if let Some(grouping_box) = self.grouping_box {
            let grouping_box = model.get_box(grouping_box).borrow();
            // @todo try recursively
            if let Some(position) = grouping_box.find_column(&expr) {
                assert!(grouping_box.ranging_quantifiers.len() == 1);
                let quantifier_id = *grouping_box.ranging_quantifiers.iter().next().unwrap();
                Ok(Expr::ColumnReference(ColumnReference {
                    quantifier_id,
                    position,
                }))
            } else {
                bail!("{} doesn't appear in the GROUP BY clause", expr);
            }
        } else {
            Ok(expr)
        }
    }
}
