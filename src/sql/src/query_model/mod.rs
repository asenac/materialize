// Copyright Materialize, Inc. and contributors. All rights reserved.
//
// Use of this software is governed by the Business Source License
// included in the LICENSE file.
//
// As of the Change Date specified in that file, in accordance with
// the Business Source License, use of this software will be governed
// by the Apache License, Version 2.0.

#![cfg(test)]

use std::cell::RefCell;
use std::collections::BTreeSet;
use std::collections::{HashMap, HashSet};
use std::fmt;

mod dot_generator;
mod generator;
mod lowering;
mod scalar_expr;

pub use scalar_expr::*;

pub type QuantifierId = usize;
pub type BoxId = usize;
pub type QuantifierSet = BTreeSet<QuantifierId>;

/// A Query Graph Model instance represents a SQL query.
#[derive(Debug)]
pub struct Model {
    /// The ID of the box representing the entry-point of the query.
    pub top_box: BoxId,
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

/// A semantic operator within a Query Graph.
#[derive(Debug)]
pub struct QueryBox {
    /// uniquely identifies the box within the model
    pub id: BoxId,
    /// the type of the box
    pub box_type: BoxType,
    /// the projection of the box
    pub columns: Vec<Column>,
    /// the input quantifiers of the box
    pub quantifiers: QuantifierSet,
    /// quantifiers ranging over this box
    pub ranging_quantifiers: QuantifierSet,
    /// whether this box must enforce the uniqueness of its output, it is
    /// guaranteed by structure of the box or it must preserve duplicated
    /// rows from its input boxes.
    pub distinct: DistinctOperation,
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
pub enum BoxType {
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
pub enum DistinctOperation {
    Enforce,
    Guaranteed,
    Preserve,
}

pub use sql_parser::ast::Ident;

#[derive(Debug)]
pub struct Quantifier {
    /// uniquely identifiers the quantifier within the model
    pub id: QuantifierId,
    /// the type of the quantifier
    pub quantifier_type: QuantifierType,
    /// the input box of this quantifier
    pub input_box: BoxId,
    /// the box that owns this quantifier
    pub parent_box: BoxId,
    /// alias for name resolution purposes
    pub alias: Option<Ident>,
}

#[derive(Debug)]
pub enum QuantifierType {
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
pub struct BaseTable {/* @todo table metadata from the catalog */}

impl BaseTable {
    fn new() -> Self {
        Self {}
    }
}

#[derive(Debug)]
pub struct Grouping {
    pub key: Vec<Box<Expr>>,
}

#[derive(Debug)]
pub struct OuterJoin {
    pub predicates: Vec<Box<Expr>>,
}

impl OuterJoin {
    fn new() -> Self {
        Self {
            predicates: Vec::new(),
        }
    }
}

#[derive(Debug)]
pub struct Select {
    pub predicates: Vec<Box<Expr>>,
    pub order_key: Option<Vec<Box<Expr>>>,
    pub limit: Option<Expr>,
    pub offset: Option<Expr>,
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
pub struct TableFunction {
    pub parameters: Vec<Box<Expr>>,
    // @todo function metadata from the catalog
}

#[derive(Debug)]
pub struct Values {
    pub rows: Vec<Vec<Box<Expr>>>,
}

#[derive(Debug)]
pub struct Column {
    pub expr: Expr,
    pub alias: Option<Ident>,
}

#[cfg(test)]
mod tests {
    use super::*;
    use dot_generator::DotGenerator;
    use expr::explain::ViewExplanation;
    use expr::DummyHumanizer;
    use generator::ModelGenerator;
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
                    let mut model = generator.generate(select).expect(test_case);

                    let dot_generator = DotGenerator::new();
                    println!("{}", dot_generator.generate(&model, test_case).unwrap());
                    // TODO there is nothing to GC here, just avoiding the warning
                    model.gargabe_collect();
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
