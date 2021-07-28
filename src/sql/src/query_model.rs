#![allow(dead_code, unused_variables)]

use anyhow::bail;
use expr::VariadicFunc;
use std::cell::{Ref, RefCell};
use std::collections::{BTreeMap, BTreeSet};
use std::collections::{HashMap, HashSet};
use std::fmt;

/// A Query Graph Model instance represents a SQL query.
#[derive(Debug)]
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
    fn visit_pre_boxes<F, E>(&self, f: &mut F) -> Result<(), E>
    where
        F: FnMut(&RefCell<QueryBox>) -> Result<(), E>,
    {
        self.visit_pre_boxes_in_subgraph(f, self.top_box)
    }

    /// Visit boxes in the query graph in pre-order
    fn visit_pre_boxes_in_subgraph<F, E>(&self, f: &mut F, start_box: BoxId) -> Result<(), E>
    where
        F: FnMut(&RefCell<QueryBox>) -> Result<(), E>,
    {
        let mut visited = HashSet::new();
        let mut stack = vec![start_box];
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
#[derive(Debug)]
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

    /// Visit all the expressions in this query box.
    fn visit_expressions<F, E>(&self, f: &mut F) -> Result<(), E>
    where
        F: FnMut(&Expr) -> Result<(), E>,
    {
        for c in self.columns.iter() {
            f(&c.expr)?;
        }
        match &self.box_type {
            BoxType::Select(select) => {
                for p in select.predicates.iter() {
                    f(p)?;
                }
                if let Some(order_key) = &select.order_key {
                    for p in order_key.iter() {
                        f(p)?;
                    }
                }
                if let Some(limit) = &select.limit {
                    f(limit)?;
                }
                if let Some(offset) = &select.offset {
                    f(offset)?;
                }
            }
            BoxType::OuterJoin(outer_join) => {
                for p in outer_join.predicates.iter() {
                    f(p)?;
                }
            }
            BoxType::Grouping(grouping) => {
                for p in grouping.key.iter() {
                    f(p)?;
                }
            }
            BoxType::Values(values) => {
                for row in values.rows.iter() {
                    for value in row.iter() {
                        f(value)?;
                    }
                }
            }
            BoxType::TableFunction(table_function) => {
                for p in table_function.parameters.iter() {
                    f(p)?;
                }
            }
            BoxType::Except | BoxType::Union | BoxType::Intersect | BoxType::BaseTable(_) => {}
        }
        Ok(())
    }
}

#[derive(Debug)]
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

#[derive(Debug)]
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

#[derive(Debug)]
struct BaseTable {/* @todo table metadata from the catalog */}

impl BaseTable {
    fn new() -> Self {
        Self {}
    }
}

#[derive(Debug)]
struct Grouping {
    key: Vec<Box<Expr>>,
}

#[derive(Debug)]
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

#[derive(Debug)]
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

#[derive(Debug)]
struct TableFunction {
    parameters: Vec<Box<Expr>>,
    // @todo function metadata from the catalog
}

#[derive(Debug)]
struct Values {
    rows: Vec<Vec<Box<Expr>>>,
}

#[derive(Debug)]
struct Column {
    expr: Expr,
    alias: Option<Ident>,
}

#[derive(Debug, PartialEq, Clone)]
enum Expr {
    ColumnReference(ColumnReference),
    BaseColumn(BaseColumn),
    CallVariadic {
        func: VariadicFunc,
        exprs: Vec<Expr>,
    },
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
            Expr::CallVariadic { func, exprs } => {
                write!(f, "{}({})", func, ore::str::separated(", ", exprs.clone()))
            }
        }
    }
}

impl Expr {
    fn collect_column_references_from_context(
        &self,
        context: &QuantifierSet,
        column_refs: &mut HashSet<ColumnReference>,
    ) {
        match &self {
            Expr::ColumnReference(c) => {
                if context.contains(&c.quantifier_id) {
                    column_refs.insert(c.clone());
                }
            }
            Expr::BaseColumn(_) => {}
            Expr::CallVariadic { func: _, exprs } => {
                for e in exprs.iter() {
                    e.collect_column_references_from_context(context, column_refs);
                }
            }
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
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

use itertools::Itertools;
use sql_parser::ast::{
    Cte, Ident, Query, Raw, SelectStatement, SetExpr, TableFactor, TableWithJoins,
};
use sql_parser::ast::{JoinConstraint, TableAlias};

struct ModelGenerator {}

impl ModelGenerator {
    fn new() -> Self {
        Self {}
    }

    fn generate(self, statement: &SelectStatement<Raw>) -> Result<Model, anyhow::Error> {
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
            }

            // make the grouping box the input of the parent select box
            let _ = self
                .model
                .make_quantifier(QuantifierType::Foreach, grouping_box, query_box);
        }

        let base_quantifiers = join_context.quantifiers;
        context.merge_quantifiers(base_quantifiers.into_iter());

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
        use sql_parser::ast;
        match expr {
            ast::Expr::Identifier(id) => self.process_identifier(id, context),
            ast::Expr::Subquery(query) => {
                let quantifier_id =
                    self.process_subquery(query, context, &join_id, QuantifierType::Scalar)?;
                // @todo multi-column scalar subqueries
                Ok(Expr::ColumnReference(ColumnReference {
                    quantifier_id,
                    position: 0,
                }))
            }
            _ => bail!("unsupported stuff"),
        }
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
    /// this context. Adds the given column to the projection of all the
    /// intermediate boxes.
    fn pullup_column_reference(&self, model: &Model, expr: Expr) -> Result<Expr, anyhow::Error> {
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
                                    bail!("{} doesn't appear in the GROUP BY clause", expr);
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

//
// Dot generator
//

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

    fn generate(mut self, model: &Model, label: &str) -> Result<String, anyhow::Error> {
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

            self.add_correlation_info(model, &b);

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
            BoxType::Values(values) => {
                for (i, row) in values.rows.iter().enumerate() {
                    r.push_str(&format!("| ROW {}: ", i));
                    for (i, value) in row.iter().enumerate() {
                        if i > 0 {
                            r.push_str(", ");
                        }
                        r.push_str(&format!("{}", value));
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

    fn add_correlation_info(&mut self, model: &Model, b: &QueryBox) {
        let mut correlation_info: BTreeMap<QuantifierId, Vec<QuantifierId>> = BTreeMap::new();
        for q_id in b.quantifiers.iter() {
            // collect the column references from the current context within
            // the subgraph under the current quantifier
            let mut column_refs = HashSet::new();
            let mut f = |inner_box: &RefCell<QueryBox>| -> Result<(), ()> {
                inner_box
                    .borrow()
                    .visit_expressions(&mut |expr: &Expr| -> Result<(), ()> {
                        expr.collect_column_references_from_context(
                            &b.quantifiers,
                            &mut column_refs,
                        );
                        Ok(())
                    })
            };
            let q = model.get_quantifier(*q_id).borrow();
            model
                .visit_pre_boxes_in_subgraph(&mut f, q.input_box)
                .unwrap();
            // collect the unique quantifiers referenced by the subgraph
            // under the current quantifier
            correlation_info.insert(
                q.id,
                column_refs
                    .iter()
                    .map(|c| c.quantifier_id)
                    .unique()
                    .collect::<Vec<_>>(),
            );
        }

        for (correlated_q, quantifiers) in correlation_info.iter() {
            for q in quantifiers.iter() {
                self.new_line(&format!(
                    "Q{0} -> Q{1} [ label = \"correlation\", style = filled, color = red ]",
                    correlated_q, q
                ));
            }
        }
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
// lowering
//

use repr::{RelationType, ScalarType};

impl Model {
    fn lower(&self) -> expr::MirRelationExpr {
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
                    .partition(|(q_id, outer_col_refs)| outer_col_refs.is_empty());

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
                relation = relation.let_in(id_gen, |id_gen, body| {
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

#[cfg(test)]
mod tests {
    use super::*;
    use expr::explain::ViewExplanation;
    use expr::DummyHumanizer;
    use sql_parser::ast::*;
    use sql_parser::parser::parse_statements;

    #[test]
    fn simple_test() {
        let test_cases = vec![
            "select * from a",
            "select * from a, b, c",
            "select * from a, (b cross join c)",
            "with b(b) as (select column1 from a) select b.b, c.b as a from b as b, b as c",
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
            "select b from a as a(a,b), lateral(select * from (values((select a.a))) as b(x))",
            "select b from a as a(a,b) union select b from b as b(a, b)",
            "select b from a as a(a,b) union all select b from b as b(a, b)",
            "select b from a as a(a,b) order by a",
            "select b from a as a(a,b) group by b",
            "select b from a as a(a,b) group by b having b",
            "select a.b from a as a(a,b) left join b as b(b, c) on a.a",
            "select a.b from a as a(a,b) right join b as b(b, c) on a.a",
            "select a.b from a as a(a,b) full join b as b(b, c) on a.a",
            "select a.b from a as a(a,b) full join b as b(b, c) on (select a.a from c as c(c, d))",
            "select a.* from (values((select column1 from b), (select column2 from c))) as a(a, b)",
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

    #[test]
    fn simple_error_test() {
        let test_cases = vec![
            // non-lateral derived tables must not see the sibling context
            "select b from a as a(a,b), (select * from (values(a.a)))",
            // this must fail with ambiguous column name error
            "select b as a, a from a as a(a, b) order by a",
        ];
        for test_case in test_cases {
            let parsed = parse_statements(test_case).unwrap();
            for stmt in parsed {
                if let Statement::Select(select) = &stmt {
                    let generator = ModelGenerator::new();
                    let _ = generator.generate(select).expect_err("expected error");
                }
            }
        }
    }

    #[test]
    fn lowering_test() {
        let test_cases = vec![
            "select * from a",
            "select * from a, b, c",
            "select * from a, (b cross join c)",
            "select a.* from a, (b cross join c)",
            "with a(a) as (select column1 from b) select b.* from a b, a c",
        ];
        for test_case in test_cases {
            let parsed = parse_statements(test_case).unwrap();
            for stmt in parsed {
                if let Statement::Select(select) = &stmt {
                    let generator = ModelGenerator::new();
                    let model = generator.generate(select).expect(test_case);

                    let relation = model.lower();
                    let explanation = ViewExplanation::new(&relation, &DummyHumanizer);
                    println!("plan for {}:", test_case);
                    println!("{}", explanation.to_string());
                }
            }
        }
    }
}
