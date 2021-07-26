#![allow(dead_code, unused_variables)]

use std::cell::{Ref, RefCell};
use std::collections::BTreeSet;
use std::collections::{HashMap, HashSet};
use std::fmt;

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
            distinct: DistinctOperation::Preserve,
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

    fn get_quantifier(&self, quantifier_id: BoxId) -> &RefCell<Quantifier> {
        &*self.quantifiers.get(&quantifier_id).unwrap()
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

    /// whether this box must enforce the uniqueness of its output, it is
    /// guaranteed by structure of the box or it must preserve duplicated
    /// rows from its input boxes.
    distinct: DistinctOperation,
}

impl QueryBox {
    fn add_predicate(&mut self, predicate: Box<Expr>) {
        match &mut self.box_type {
            BoxType::Select(select) => select.predicates.push(predicate),
            BoxType::OuterJoin(outer_join) => outer_join.predicates.push(predicate),
            _ => panic!("invalid box type"),
        }
    }

    fn get_predicates<'a>(&'a self) -> Option<&'a Vec<Box<Expr>>> {
        match &self.box_type {
            BoxType::Select(select) => Some(&select.predicates),
            BoxType::OuterJoin(outer_join) => Some(&outer_join.predicates),
            _ => None,
        }
    }

    fn add_column_if_not_exists(&mut self, expr: Expr, alias: Option<Ident>) -> usize {
        for (position, c) in self.columns.iter().enumerate() {
            if c.expr == expr {
                return position;
            }
        }
        let position = self.columns.len();
        self.columns.push(Column { expr, alias });
        position
    }

    fn find_column(&self, expr: &Expr) -> Option<usize> {
        for (position, c) in self.columns.iter().enumerate() {
            if c.expr == *expr {
                return Some(position);
            }
        }
        None
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

impl BoxType {
    fn get_box_type_str(&self) -> &'static str {
        match self {
            BoxType::BaseTable(..) => "BaseTable",
            BoxType::Except => "Except",
            BoxType::Grouping(..) => "Grouping",
            BoxType::Intersect => "Intersect",
            BoxType::OuterJoin(..) => "OuterJoin",
            BoxType::Select(..) => "Select",
            BoxType::TableFunction(..) => "TableFunction",
            BoxType::Union => "Union",
            BoxType::Values(..) => "Values",
        }
    }
}

#[derive(Debug)]
enum DistinctOperation {
    Enforce,
    Guaranteed,
    Preserve,
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

#[derive(Debug)]
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

impl fmt::Display for QuantifierType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self {
            QuantifierType::Foreach => write!(f, "F"),
            QuantifierType::PreservedForeach => write!(f, "P"),
            QuantifierType::Existential => write!(f, "E"),
            QuantifierType::All => write!(f, "All"),
            QuantifierType::Any => write!(f, "Any"),
            QuantifierType::Scalar => write!(f, "S"),
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

#[derive(Debug, PartialEq, Clone)]
enum Expr {
    ColumnReference(ColumnReference),
    BaseColumn(BaseColumn),
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self {
            Expr::ColumnReference(c) => {
                write!(f, "Q{}.C{}", c.quantifier_id, c.position)
            }
            Expr::BaseColumn(c) => {
                write!(f, "C{}", c.position)
            }
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
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

#[derive(Debug, PartialEq, Clone)]
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
        // @todo limit, offset
        if !query.order_by.is_empty() {
            let mut key = Vec::new();
            for key_item in query.order_by.iter() {
                // @todo direction
                let expr = self.process_expr(&key_item.expr, &current_context)?;
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
    ) -> Result<(), String> {
        // @todo CTEs can see previous CTEs within the same list
        for cte in ctes.iter() {
            let cte_id = self.process_query(&cte.query, context.parent_context.clone())?;
            // @todo add intermediate box with column aliases
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
    ) -> Result<(), String> {
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
                let left_box = {
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

                let right_box = {
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
                // @todo add columns from the left box

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
    ) -> Result<(), String> {
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
            let predicate = self.process_expr(&selection, &join_context)?;
            self.model
                .get_box(join_box)
                .borrow_mut()
                .add_predicate(Box::new(predicate));
        }

        // @todo grouping, having, distinct

        if is_grouping {
            let mut grouping_key = Vec::new();
            for key_item in select.group_by.iter() {
                let key_item = self.process_expr(&key_item, &join_context)?;
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
            }

            // make the grouping box the input of the parent select box
            let _ = self
                .model
                .make_quantifier(QuantifierType::Foreach, grouping_box, query_box);
        }

        let base_quantifiers = join_context.quantifiers;
        context.merge_quantifiers(base_quantifiers.into_iter());

        if let Some(having) = &select.having {
            let predicate = self.process_expr(having, context)?;
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
                _ => return Err(format!("@todo unsupported stuff")),
            }
        }
        Ok(())
    }

    fn process_projection(
        &mut self,
        projection: &Vec<sql_parser::ast::SelectItem<Raw>>,
        query_box: BoxId,
        context: &mut NameResolutionContext,
    ) -> Result<(), String> {
        use sql_parser::ast;
        for si in projection {
            match si {
                ast::SelectItem::Wildcard => {
                    self.model
                        .get_box(query_box)
                        .borrow_mut()
                        .add_all_input_columns(self.model);
                }
                ast::SelectItem::Expr {
                    expr: ast::Expr::QualifiedWildcard(table_name),
                    alias: _,
                } => {
                    // @todo qualified tables
                    if let Some((context, quantifier_id)) =
                        context.resolve_quantifier(self.model, table_name.last().unwrap())
                    {
                        let input_box_id =
                            self.model.get_quantifier(quantifier_id).borrow().input_box;
                        let input_box = self.model.get_box(input_box_id).borrow();
                        for (position, c) in input_box.columns.iter().enumerate() {
                            let expr = Expr::ColumnReference(ColumnReference {
                                quantifier_id,
                                position,
                            });
                            let expr = context.pullup_column_reference(self.model, expr)?;
                            self.model
                                .get_box(query_box)
                                .borrow_mut()
                                .columns
                                .push(Column {
                                    expr,
                                    alias: c.alias.clone(),
                                });
                        }
                    } else {
                        return Err(format!("unknown table {:?}", table_name));
                    }
                }
                ast::SelectItem::Expr { expr, alias } => {
                    let expr = self.process_expr(expr, context)?;
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

                if alias.is_none() {
                    let child_quantifiers = join_context.quantifiers;
                    context.merge_quantifiers(child_quantifiers.into_iter());
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
                let prev_lateral_flag = context.is_lateral;
                context.is_lateral = *lateral;
                let parent_context = if *lateral {
                    Some(&*context)
                } else {
                    context.parent_context.clone()
                };
                let box_id = self.process_query(&subquery, parent_context)?;
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
                mut_join.add_predicate(Box::new(expr));
                mut_join.add_all_input_columns(self.model);
            }
            _ => return Err(format!("unsupported stuff")),
        }
        Ok(())
    }

    fn process_values(
        &mut self,
        values: &sql_parser::ast::Values<Raw>,
        query_box: BoxId,
        context: &mut NameResolutionContext,
    ) -> Result<(), String> {
        let mut rows = Vec::with_capacity(values.0.len());
        for values in values.0.iter() {
            let mut row = Vec::with_capacity(values.len());
            for value in values.iter() {
                let expr = self.process_expr(value, context)?;
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
    ) -> Result<Expr, String> {
        use sql_parser::ast;
        match expr {
            ast::Expr::Identifier(id) => Ok(context.resolve_column(&self.model, id)?),
            _ => Err(format!("unsupported stuff")),
        }
    }

    /// @todo support for RawName::Id
    fn extract_name(&self, name: &sql_parser::ast::RawName) -> Result<Ident, String> {
        let name = match name {
            sql_parser::ast::RawName::Name(c) => c.0.last().cloned().unwrap(),
            _ => return Err(format!("unsupported")),
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

    /// return the column alias/name of the column projected in the given position
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

    /// Creates a new context for an intermediate join.
    fn for_join(join_box: BoxId, sibling_context: &'a NameResolutionContext<'a>) -> Self {
        Self {
            owner_box: join_box,
            quantifiers: Vec::new(),
            ctes: HashMap::new(),
            parent_context: sibling_context.parent_context.clone(),
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

    fn resolve_column(&self, model: &Model, name: &Vec<Ident>) -> Result<Expr, String> {
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

        Err(format!("column {:?} could not be resolved", name))
    }

    /// Resolve the column identified by name against the quantifiers in this context.
    /// Returns a column reference expression if found. Checks whether the column name
    /// is ambiguous within the current context.
    fn resolve_column_in_context(
        &self,
        model: &Model,
        name: &Vec<Ident>,
    ) -> Result<Option<Expr>, String> {
        let expr = match name.len() {
            1 => {
                let mut found = None;
                for quantifier_id in self.quantifiers.iter() {
                    if let Some(expr) =
                        self.resolve_column_in_quantifier(model, *quantifier_id, &name[0])?
                    {
                        if found.is_some() {
                            return Err(format!("ambiguous column name {:?}", name));
                        }
                        found = Some(expr);
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
            _ => return Err(format!("unsupported stuff")),
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
    ) -> Result<Option<Expr>, String> {
        let q = model.get_quantifier(quantifier_id).borrow();
        let input_box = model.get_box(q.input_box).borrow();
        let mut found = None;
        for (position, c) in input_box.columns.iter().enumerate() {
            if let Some(alias) = &c.alias {
                if alias == name {
                    if found.is_some() {
                        return Err(format!("ambiguous column name {}", name));
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
    /// this context. Adds the given column to the projection of all the
    /// intermediate boxex.
    fn pullup_column_reference(&self, model: &Model, expr: Expr) -> Result<Expr, String> {
        match expr {
            Expr::ColumnReference(mut c) => {
                loop {
                    let q = model.get_quantifier(c.quantifier_id).borrow();
                    if q.parent_box == self.owner_box {
                        break;
                    }
                    let parent_q_id = {
                        let parent_box = model.get_box(q.parent_box).borrow();
                        assert!(parent_box.ranging_quantifiers.len() == 1);
                        *parent_box.ranging_quantifiers.iter().next().unwrap()
                    };

                    let alias = {
                        let b = model.get_box(q.input_box).borrow();
                        b.columns[c.position].alias.clone()
                    };
                    c.position = {
                        let mut parent_box = model.get_box(q.parent_box).borrow_mut();
                        let expr = Expr::ColumnReference(c.clone());
                        match &parent_box.box_type {
                            BoxType::Select(_) | BoxType::OuterJoin(_) => {
                                parent_box.add_column_if_not_exists(expr, alias)
                            }
                            BoxType::Grouping(_) => {
                                // @todo special case for grouping boxes.
                                if let Some(position) = parent_box.find_column(&expr) {
                                    position
                                } else {
                                    return Err(format!(
                                        "{} doesn't appear in the GROUP BY clause",
                                        expr
                                    ));
                                }
                            }
                            _ => panic!("unexpected box type"),
                        }
                    };
                    c.quantifier_id = parent_q_id;
                }
                Ok(Expr::ColumnReference(c.clone()))
            }
            _ => panic!("expected column reference"),
        }
    }
}

struct DotGenerator {
    output: String,
    indent: u32,
}

impl DotGenerator {
    fn new() -> Self {
        Self {
            output: String::new(),
            indent: 0,
        }
    }

    fn generate(mut self, model: &Model, label: &str) -> Result<String, String> {
        self.new_line("digraph G {");
        self.inc();
        self.new_line("compound = true");
        self.new_line("labeljust = l");
        self.new_line(&format!("label=\"{}\"", label));
        self.new_line("node [ shape = box ]");

        let mut box_stack = vec![model.top_box];
        let mut quantifiers = Vec::new();
        let mut visited_boxes = HashSet::new();
        while let Some(box_id) = box_stack.pop() {
            if !visited_boxes.insert(box_id) {
                continue;
            }

            let b = model.get_box(box_id).borrow();

            self.new_line(&format!("subgraph cluster{} {{", box_id));
            self.inc();
            self.new_line(&format!(
                "label = \"Box{}:{}\"",
                box_id,
                Self::get_box_title(&b)
            ));
            self.new_line(&format!(
                "boxhead{} [ shape = record, label=\"{{ {} }}\" ]",
                box_id,
                Self::get_box_head(&b)
            ));

            self.new_line("{");
            self.inc();
            self.new_line("rank = same");

            if b.quantifiers.len() > 0 {
                self.new_line("node [ shape = circle ]");
            }

            for q_id in b.quantifiers.iter() {
                quantifiers.push(*q_id);

                let q = model.get_quantifier(*q_id).borrow();
                box_stack.push(q.input_box);
                self.new_line(&format!(
                    "Q{0} [ label=\"Q{0}({1}){2}\" ]",
                    q_id,
                    q.quantifier_type,
                    Self::get_quantifier_alias(&q)
                ));
            }

            self.dec();
            self.new_line("}");
            self.dec();
            self.new_line("}");
        }

        if quantifiers.len() > 0 {
            self.new_line("edge [ arrowhead = none, style = dashed ]");
            for q_id in quantifiers.iter() {
                let q = model.get_quantifier(*q_id).borrow();
                self.new_line(&format!(
                    "Q{0} -> boxhead{1} [ lhead = cluster{1} ]",
                    q_id, q.input_box
                ));
            }
        }

        self.dec();
        self.new_line("}");
        self.new_line(""); // final empty line
        Ok(self.output)
    }

    fn get_box_title(b: &QueryBox) -> &'static str {
        b.box_type.get_box_type_str()
    }

    fn get_box_head(b: &QueryBox) -> String {
        let mut r = String::new();

        r.push_str(&format!("Distinct: {:?}", b.distinct));

        for (i, c) in b.columns.iter().enumerate() {
            r.push_str(&format!("| {}: {}", i, c.expr));
            if let Some(c) = &c.alias {
                r.push_str(&format!(" as {}", c.as_str()));
            }
        }

        match &b.box_type {
            BoxType::Select(select) => {
                if let Some(order_key) = &select.order_key {
                    r.push_str("| ORDER BY: ");
                    for (i, key_item) in order_key.iter().enumerate() {
                        if i > 0 {
                            r.push_str(", ");
                        }
                        // @todo direction
                        r.push_str(&format!("{}", key_item));
                    }
                }
            }
            BoxType::Grouping(grouping) => {
                if !grouping.key.is_empty() {
                    r.push_str("| GROUP BY: ");
                    for (i, key_item) in grouping.key.iter().enumerate() {
                        if i > 0 {
                            r.push_str(", ");
                        }
                        r.push_str(&format!("{}", key_item));
                    }
                }
            }
            _ => {}
        }

        // @todo predicates as arrows
        if let Some(predicates) = b.get_predicates() {
            for predicate in predicates.iter() {
                r.push_str(&format!("| {}", predicate));
            }
        }

        r
    }

    fn get_quantifier_alias(q: &Quantifier) -> String {
        if let Some(alias) = &q.alias {
            format!(" as {}", alias)
        } else {
            "".to_string()
        }
    }

    fn inc(&mut self) {
        self.indent += 1;
    }

    fn dec(&mut self) {
        self.indent -= 1;
    }

    fn append(&mut self, s: &str) {
        self.output.push_str(s);
    }

    fn new_line(&mut self, s: &str) {
        if !self.output.is_empty() && self.output.rfind('\n') != Some(self.output.len()) {
            self.end_line();
            for _ in 0..self.indent * 4 {
                self.output.push(' ');
            }
        }
        self.output.push_str(s);
    }

    fn end_line(&mut self) {
        self.output.push('\n');
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
            "select * from a, b, c",
            "select * from a, (b cross join c)",
            // "with b(b) as (select column1 from a) select b from b, c",
            "select * from a inner join b on a.column1, c",
            "select * from a, lateral(select * from b inner join c on a.column1)",
            "select * from a as a(a,b), lateral(select * from b inner join c on a.a)",
            "select b from a as a(a,b)",
            "select a.b from a as a(a,b), d cross join lateral(select a.a, a.b as z from b inner join c on a.a) where a.a",
            "select a.* from a as a(a,b)",
            "select distinct a.* from a as a(a,b)",
            "select distinct a.* from a as a(a,b), b as b(b,c), c as c(c, d) cross join (d as d(d, e) cross join (f as f(f, h) cross join lateral(select e.e from e as e(e, f))))",
            "select distinct a.* from a as a(a,b), b as b(b,c), c as c(c, d) cross join (d as d(d, e) cross join (f as f(f, h) cross join lateral(select a.a, b.b, c.c, d.d, e.e, f.f from e as e(e, f))))",
            "select distinct a.* from a as a(a,b), b as b(b,c), c as c(c, d) cross join (d as d(d, e) cross join (f as f(f, h) cross join lateral(select a.*, b.*, c.*, d.*, e.*, f.* from e as e(e, f))))",
            "select b from a as a(a,b), lateral(select * from (values(a.a)))",
            "select b from a as a(a,b), lateral(select * from (values(a.a)) as b(x))",
            "select b from a as a(a,b) union select b from b as b(a, b)",
            "select b from a as a(a,b) union all select b from b as b(a, b)",
            "select b from a as a(a,b) order by a",
            "select b from a as a(a,b) group by b",
            "select b from a as a(a,b) group by b having b",
        ];
        for test_case in test_cases {
            let parsed = parse_statements(test_case).unwrap();
            for stmt in parsed {
                if let Statement::Select(select) = &stmt {
                    let generator = ModelGenerator::new();
                    let model = generator.generate(select).expect(test_case);

                    let dot_generator = DotGenerator::new();
                    println!("{}", dot_generator.generate(&model, test_case).unwrap());
                }
            }
        }
    }
}
