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
    Enforced,
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

#[derive(Debug)]
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

#[derive(Debug)]
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

#[derive(Debug)]
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
        self.model
            .get_box(query_box)
            .borrow_mut()
            .add_all_input_columns(self.model);
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
        context: &NameResolutionContext,
    ) -> Result<Box<Expr>, String> {
        use sql_parser::ast;
        match expr {
            ast::Expr::Identifier(id) => Ok(Box::new(context.resolve_column(&self.model, id)?)),
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

    fn resolve_column(&self, model: &Model, name: &Vec<Ident>) -> Result<Expr, String> {
        if let Some(expr) = self.resolve_column_in_context(model, name)? {
            return Ok(expr);
        }

        if self.is_lateral {
            if let Some(sibling) = &self.sibling_context {
                if let Some(expr) = sibling.resolve_column_in_context(model, name)? {
                    return Ok(expr);
                }
            }
        }

        if let Some(parent) = &self.parent_context {
            return parent.resolve_column(model, name);
        }

        Err(format!("column {:?} could not be resolved", name))
    }

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
                    return Err(format!("unknown relation name {}", &name[0]));
                }
            }
            _ => return Err(format!("unsupported stuff")),
        };

        Ok(expr)
    }

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
            // @todo pullup_column_reference
            Ok(Some(expr))
        } else {
            Ok(None)
        }
    }

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
    fn resolve_quantifier_recursively(&self, model: &Model, name: &Ident) -> Option<QuantifierId> {
        if let Some(q_id) = self.resolve_quantifier_in_context(model, name) {
            return Some(q_id);
        }

        if self.is_lateral {
            if let Some(sibling) = &self.sibling_context {
                if let Some(q_id) = sibling.resolve_quantifier_in_context(model, name) {
                    return Some(q_id);
                }
            }
        }

        if let Some(parent) = &self.parent_context {
            return parent.resolve_quantifier_recursively(model, name);
        }
        None
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
            "with b(b) as (select f1 from a) select b from b, c",
        ];
        for test_case in test_cases {
            let parsed = parse_statements(test_case).unwrap();
            for stmt in parsed {
                if let Statement::Select(select) = &stmt {
                    let generator = ModelGenerator::new();
                    let model = generator.generate(select).unwrap();

                    let dot_generator = DotGenerator::new();
                    println!("{}", dot_generator.generate(&model, test_case).unwrap());
                }
            }
        }
    }
}
