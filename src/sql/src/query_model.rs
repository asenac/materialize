#![allow(dead_code, unused_variables)]

use std::cell::{Ref, RefCell};
use std::collections::BTreeSet;
use std::collections::{HashMap, HashSet};

/// A Query Graph Model instance represents a SQL query.
struct Model {
    /// The ID of the box representing the entry-point of the query.
    top_box: BoxId,
    /// All boxes in the query graph model.
    boxes: HashMap<BoxId, Box<RefCell<QueryBox>>>,
    /// Used for asigning unique IDs to query boxes.
    next_box_id: usize,
    /// All quantifiers in the query graph model.
    quantifiers: HashMap<QuantifierId, Box<RefCell<Quantifier>>>,
    /// Used for asigning unique IDs to quantifiers.
    next_quantifier_id: usize,
}

impl Model {
    fn new() -> Self {
        Self {
            top_box: 0,
            boxes: HashMap::new(),
            next_box_id: 0,
            quantifiers: HashMap::new(),
            next_quantifier_id: 0,
        }
    }

    fn make_box(&mut self, box_type: BoxType) -> BoxId {
        let id = self.next_box_id;
        self.next_box_id += 1;
        let b = Box::new(RefCell::new(QueryBox {
            id,
            box_type,
            columns: Vec::new(),
            quantifiers: QuantifierSet::new(),
            ranging_quantifiers: QuantifierSet::new(),
        }));
        self.boxes.insert(id, b);
        id
    }

    fn make_select_box(&mut self) -> BoxId {
        self.make_box(BoxType::Select(Select::new()))
    }

    fn get_box(&self, box_id: BoxId) -> &RefCell<QueryBox> {
        &*self.boxes.get(&box_id).unwrap()
    }

    /// Create a new quantifier and adds it to the parent box
    fn make_quantifier(
        &mut self,
        quantifier_type: QuantifierType,
        input_box: BoxId,
        parent_box: BoxId,
    ) -> QuantifierId {
        let id = self.next_quantifier_id;
        self.next_quantifier_id += 1;
        let q = Box::new(RefCell::new(Quantifier {
            id,
            quantifier_type,
            input_box,
            parent_box,
            alias: None,
        }));
        self.quantifiers.insert(id, q);
        self.get_box(parent_box).borrow_mut().quantifiers.insert(id);
        self.get_box(input_box)
            .borrow_mut()
            .ranging_quantifiers
            .insert(id);
        id
    }

    fn get_quantifier(&self, box_id: BoxId) -> &RefCell<Quantifier> {
        &*self.quantifiers.get(&box_id).unwrap()
    }

    /// Visit boxes in the query graph in pre-order
    fn visit_pre_boxes<F, E>(&self, mut f: F) -> Result<(), E>
    where
        F: FnMut(&RefCell<QueryBox>) -> Result<(), E>,
    {
        let mut visited = HashSet::new();
        let mut stack = vec![self.top_box];
        while !stack.is_empty() {
            let box_id = stack.pop().unwrap();
            if visited.insert(box_id) {
                let query_box = self.get_box(box_id);
                f(query_box)?;

                stack.extend(
                    query_box
                        .borrow()
                        .quantifiers
                        .iter()
                        .rev()
                        .map(|q| self.get_quantifier(*q).borrow().input_box),
                );
            }
        }
        Ok(())
    }

    /// Removes unreferenced objects from the model. May be invoked
    /// several times during query rewrites.
    fn gargabe_collect(&mut self) {
        let mut visited_boxes = HashSet::new();
        let mut visited_quantifiers = HashSet::new();
        let mut stack = vec![self.top_box];
        while !stack.is_empty() {
            let box_id = stack.pop().unwrap();
            if visited_boxes.insert(box_id) {
                let query_box = self.get_box(box_id);
                for q in query_box.borrow().quantifiers.iter() {
                    visited_quantifiers.insert(*q);
                    let q = self.get_quantifier(*q).borrow();
                    stack.push(q.input_box);
                }
            }
        }
        self.boxes.retain(|b, _| visited_boxes.contains(b));
        self.quantifiers
            .retain(|q, _| visited_quantifiers.contains(q));
    }
}

type QuantifierId = usize;
type BoxId = usize;
type QuantifierSet = BTreeSet<QuantifierId>;

/// A semantic operator within a Query Graph.
struct QueryBox {
    /// uniquely identifies the box within the model
    id: BoxId,
    /// the type of the box
    box_type: BoxType,
    /// the projection of the box
    columns: Vec<Column>,
    /// the input quantifiers of the box
    quantifiers: QuantifierSet,
    /// quantifiers ranging over this box
    ranging_quantifiers: QuantifierSet,
}

impl QueryBox {
    fn add_predicate(&mut self, predicate: Box<Expr>) {
        match &mut self.box_type {
            BoxType::Select(select) => select.predicates.push(predicate),
            BoxType::OuterJoin(outer_join) => outer_join.predicates.push(predicate),
            _ => panic!("invalid box type"),
        }
    }

    /// Add all columns from the non-subquery input quantifiers of the box to the
    /// projection of the box.
    fn add_all_input_columns(&mut self, model: &Model) {
        for quantifier_id in self.quantifiers.iter() {
            let q = model.get_quantifier(*quantifier_id);
            let bq = q.borrow();
            if !bq.quantifier_type.is_subquery() {
                let input_box = model.get_box(bq.input_box).borrow();
                for (position, c) in input_box.columns.iter().enumerate() {
                    let expr = Expr::ColumnReference(ColumnReference {
                        quantifier_id: *quantifier_id,
                        position,
                    });
                    self.columns.push(Column {
                        expr,
                        alias: c.alias.clone(),
                    });
                }
            }
        }
    }
}

enum BoxType {
    BaseTable(BaseTable),
    Except,
    Grouping(Grouping),
    Intersect,
    OuterJoin(OuterJoin),
    Select(Select),
    TableFunction(TableFunction),
    Union,
    Values(Values),
}

// pub use sql_parser::ast::Ident;

struct Quantifier {
    /// uniquely identifiers the quantifier within the model
    id: QuantifierId,
    /// the type of the quantifier
    quantifier_type: QuantifierType,
    /// the input box of this quantifier
    input_box: BoxId,
    /// the box that owns this quantifier
    parent_box: BoxId,
    /// alias for name resolution purposes
    alias: Option<Ident>,
}

enum QuantifierType {
    All,
    Any,
    Existential,
    Foreach,
    PreservedForeach,
    Scalar,
}

impl QuantifierType {
    fn is_subquery(&self) -> bool {
        match self {
            QuantifierType::All
            | QuantifierType::Any
            | QuantifierType::Existential
            | QuantifierType::Scalar => true,
            _ => false,
        }
    }
}

struct BaseTable {/* @todo table metadata from the catalog */}

impl BaseTable {
    fn new() -> Self {
        Self {}
    }
}

struct Grouping {
    key: Vec<Box<Expr>>,
}

struct OuterJoin {
    predicates: Vec<Box<Expr>>,
}

impl OuterJoin {
    fn new() -> Self {
        Self {
            predicates: Vec::new(),
        }
    }
}

struct Select {
    predicates: Vec<Box<Expr>>,
    order_key: Option<Vec<Box<Expr>>>,
    limit: Option<Expr>,
    offset: Option<Expr>,
}

impl Select {
    fn new() -> Self {
        Self {
            predicates: Vec::new(),
            order_key: None,
            limit: None,
            offset: None,
        }
    }
}

struct TableFunction {
    parameters: Vec<Box<Expr>>,
    // @todo function metadata from the catalog
}

struct Values {
    rows: Vec<Vec<Box<Expr>>>,
}

struct Column {
    expr: Expr,
    alias: Option<Ident>,
}

enum Expr {
    ColumnReference(ColumnReference),
    BaseColumn(BaseColumn),
}

struct ColumnReference {
    quantifier_id: QuantifierId,
    position: usize,
}

impl ColumnReference {
    fn dereference<'a>(&self, model: &'a Model) -> ColumnRef<'a> {
        let input_box = model.get_quantifier(self.quantifier_id).borrow().input_box;
        let input_box = model.get_box(input_box).borrow();
        ColumnRef {
            query_box: input_box,
            position: self.position,
        }
    }
}

struct ColumnRef<'a> {
    query_box: Ref<'a, QueryBox>,
    position: usize,
}

impl<'a> std::ops::Deref for ColumnRef<'a> {
    type Target = Expr;

    fn deref(&self) -> &Self::Target {
        &self.query_box.columns[self.position].expr
    }
}

struct BaseColumn {
    position: usize,
}

//
// Model generator
//

use sql_parser::ast::{
    Cte, Ident, Query, Raw, SelectStatement, SetExpr, TableFactor, TableWithJoins,
};
use sql_parser::ast::{JoinConstraint, TableAlias};

struct ModelGenerator {}

impl ModelGenerator {
    fn new() -> Self {
        Self {}
    }

    fn generate(self, statement: &SelectStatement<Raw>) -> Result<Model, String> {
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

    fn process_top_level_query(mut self, query: &Query<Raw>) -> Result<(), String> {
        let top_box = self.process_query(query, None)?;
        self.model.top_box = top_box;
        Ok(())
    }

    fn process_query(
        &mut self,
        query: &Query<Raw>,
        parent_context: Option<&NameResolutionContext>,
    ) -> Result<BoxId, String> {
        let box_id = self.model.make_select_box();
        let mut current_context = NameResolutionContext::new(box_id, parent_context);
        self.add_ctes_to_context(&query.ctes, &mut current_context)?;
        self.process_query_body(&query.body, box_id, &mut current_context)?;
        // @todo order by, limit, offset
        Ok(box_id)
    }

    fn add_ctes_to_context(
        &mut self,
        ctes: &Vec<Cte<Raw>>,
        context: &mut NameResolutionContext,
    ) -> Result<(), String> {
        // @todo CTEs can see previous CTEs within the same list
        for cte in ctes.iter() {
            let cte_id = self.process_query(&cte.query, context.parent_context.clone())?;
            // @todo add intermediate box with column aliases
            context.ctes.insert(cte.alias.name.clone(), cte_id);
        }
        Ok(())
    }

    fn process_query_body(
        &mut self,
        body: &SetExpr<Raw>,
        query_box: BoxId,
        context: &mut NameResolutionContext,
    ) -> Result<(), String> {
        match body {
            SetExpr::Select(select) => self.process_select(&*select, query_box, context),
            _ => Err(format!("@todo unsupported stuff")),
        }
    }

    fn process_select(
        &mut self,
        select: &sql_parser::ast::Select<Raw>,
        query_box: BoxId,
        context: &mut NameResolutionContext,
    ) -> Result<(), String> {
        self.process_from_clause(&select.from, query_box, context)?;
        if let Some(selection) = &select.selection {
            let predicate = self.process_expr(&selection, context)?;
            self.model
                .get_box(query_box)
                .borrow_mut()
                .add_predicate(predicate);
        }
        // @todo grouping, having, projection, distinct
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
    ) -> Result<(), String> {
        for twj in from.iter() {
            self.process_comma_join_operand(&twj, context)?;
        }
        Ok(())
    }

    /// Process comma-join operands and nested joins. Returns the box id of the
    /// box representing the join.
    fn process_comma_join_operand(
        &mut self,
        twj: &TableWithJoins<Raw>,
        context: &mut NameResolutionContext,
    ) -> Result<(), String> {
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
    ) -> Result<QuantifierId, String> {
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

            let mut join_context =
                NameResolutionContext::for_join(join_id, context.parent_context.clone(), context);

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

            let child_quantifiers = join_context.quantifiers;
            context.merge_quantifiers(child_quantifiers.into_iter());

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
    ) -> Result<QuantifierId, String> {
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
                            alias: Some(Ident::new(format!("COLUMN{}", i + 1))),
                        });
                    }
                    (box_id, true, alias.clone())
                }
            }
            TableFactor::NestedJoin { join, alias } => {
                let join_id = self.model.make_select_box();
                let mut join_context = NameResolutionContext::for_join(
                    join_id,
                    context.parent_context.clone(),
                    context,
                );

                self.process_comma_join_operand(join, &mut join_context)?;

                if alias.is_none() {
                    let child_quantifiers = join_context.quantifiers;
                    context.merge_quantifiers(child_quantifiers.into_iter());
                }

                (join_id, alias.is_some(), alias.clone())
            }
            TableFactor::Derived {
                lateral,
                subquery,
                alias,
            } => {
                let prev_lateral_flag = context.is_lateral;
                context.is_lateral = *lateral;
                let box_id = self.process_query(&subquery, Some(context))?;
                context.is_lateral = prev_lateral_flag;

                (box_id, true, alias.clone())
            }
            _ => return Err(format!("unsupported stuff")),
        };

        if let Some(alias) = &alias {
            if alias.strict
                && alias.columns.len() != self.model.get_box(box_id).borrow().columns.len()
            {
                return Err(format!("column number mismatch"));
            }
            // add intermediate select box with the column aliases
            if !alias.columns.is_empty() {
                let select_id = self.model.make_select_box();
                let quantifier_id =
                    self.model
                        .make_quantifier(QuantifierType::Foreach, box_id, select_id);
                let mut select = self.model.get_box(select_id).borrow_mut();
                for (position, c) in alias.columns.iter().enumerate() {
                    select.columns.push(Column {
                        expr: Expr::ColumnReference(ColumnReference {
                            quantifier_id,
                            position,
                        }),
                        alias: Some(c.clone()),
                    });
                }
                box_id = select_id;
            }
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
    ) -> Result<(), String> {
        match constraint {
            JoinConstraint::On(expr) => {
                let expr = self.process_expr(expr, context)?;
                let join = self.model.get_box(join_id);
                let mut mut_join = join.borrow_mut();
                mut_join.add_predicate(expr);
                mut_join.add_all_input_columns(self.model);
            }
            _ => return Err(format!("unsupported stuff")),
        }
        Ok(())
    }

    fn process_expr(
        &mut self,
        expr: &sql_parser::ast::Expr<Raw>,
        context: &mut NameResolutionContext,
    ) -> Result<Box<Expr>, String> {
        Err(format!("unsupported stuff"))
    }

    /// @todo support for RawName::Id
    fn extract_name(&self, name: &sql_parser::ast::RawName) -> Result<Ident, String> {
        let name = match name {
            sql_parser::ast::RawName::Name(c) => c.0.last().cloned().unwrap(),
            _ => return Err(format!("unsupported")),
        };
        Ok(name)
    }
}

struct NameResolutionContext<'a> {
    owner_box: BoxId,
    /// leaf quantifiers for resolving column names
    quantifiers: Vec<QuantifierId>,
    /// CTEs visibile within this context
    ctes: HashMap<Ident, BoxId>,
    /// an optional parent context
    parent_context: Option<&'a NameResolutionContext<'a>>,
    /// the sibling context: only visible if `is_lateral` is true
    sibling_context: Option<&'a NameResolutionContext<'a>>,
    /// enables/disables the visibility of the sibling scope
    is_lateral: bool,
}

impl<'a> NameResolutionContext<'a> {
    fn new(owner_box: BoxId, parent_context: Option<&'a NameResolutionContext<'a>>) -> Self {
        Self {
            owner_box,
            quantifiers: Vec::new(),
            ctes: HashMap::new(),
            parent_context,
            sibling_context: None,
            is_lateral: false,
        }
    }

    fn for_join(
        join_box: BoxId,
        parent_context: Option<&'a NameResolutionContext<'a>>,
        sibling_context: &'a NameResolutionContext<'a>,
    ) -> Self {
        Self {
            owner_box: join_box,
            quantifiers: Vec::new(),
            ctes: HashMap::new(),
            parent_context,
            sibling_context: Some(sibling_context),
            is_lateral: false,
        }
    }

    fn merge_quantifiers<I>(&mut self, quantifiers: I)
    where
        I: IntoIterator<Item = QuantifierId>,
    {
        self.quantifiers.extend(quantifiers);
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
}

//
// Dot generator
//

#[cfg(test)]
mod tests {
    use super::*;
    use sql_parser::ast::*;
    use sql_parser::parser::parse_statements;

    #[test]
    fn simple_test() {
        let test_cases = vec![
            "select * from a",
            "with b(b) as (select a from a) select b from b",
        ];
        for test_case in test_cases {
            let parsed = parse_statements(test_case).unwrap();
            for stmt in parsed {
                if let Statement::Select(select) = &stmt {
                    let generator = ModelGenerator::new();
                    let model = generator.generate(select).unwrap();
                }
            }
        }
    }
}
