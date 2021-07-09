#![allow(dead_code, unused_variables)]

use std::collections::BTreeSet;
use std::collections::HashMap;

struct Model {
    top_box: BoxId,
    boxes: HashMap<BoxId, Box<QueryBox>>,
    next_box_id: usize,
    quantifiers: HashMap<QuantifierId, Box<Quantifier>>,
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

    fn make_box<'a>(&'a mut self, box_type: BoxType) -> BoxId {
        let id = self.next_box_id;
        self.next_box_id += 1;
        let b = Box::new(QueryBox {
            id,
            box_type,
            columns: Vec::new(),
            quantifiers: QuantifierSet::new(),
            ranging_quantifiers: QuantifierSet::new(),
        });
        self.boxes.insert(id, b);
        id
    }

    fn make_select_box<'a>(&'a mut self) -> BoxId {
        self.make_box(BoxType::Select(Select::new()))
    }

    fn get_box<'a>(&'a self, box_id: BoxId) -> &'a QueryBox {
        &*self.boxes.get(&box_id).unwrap()
    }

    fn get_box_mut<'a>(&'a mut self, box_id: BoxId) -> &'a QueryBox {
        &mut *self.boxes.get_mut(&box_id).unwrap()
    }
}

type QuantifierId = usize;
type BoxId = usize;
type QuantifierSet = BTreeSet<QuantifierId>;

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
    alias: Option<String>,
}

enum QuantifierType {
    All,
    Any,
    Existential,
    Foreach,
    PreservedForeach,
    Scalar,
}

struct BaseTable {/* @todo table metadata from the catalog */}

struct Grouping {
    key: Vec<Box<Expr>>,
}

struct OuterJoin {
    predicates: Vec<Box<Expr>>,
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
    alias: Option<String>,
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
    fn dereference<'a>(&self, model: &'a Model) -> &'a Expr {
        let input_box = model
            .quantifiers
            .get(&self.quantifier_id)
            .unwrap()
            .input_box;
        &model.boxes.get(&input_box).unwrap().columns[self.position].expr
    }
}

struct BaseColumn {
    position: usize,
}

//
// Model generator
//

use sql_parser::ast::{AstInfo, Cte, Ident, Query, SelectStatement, SetExpr, TableWithJoins};

struct ModelGenerator {}

impl ModelGenerator {
    fn new() -> Self {
        Self {}
    }

    fn generate<T: AstInfo>(self, statement: &SelectStatement<T>) -> Result<Model, String> {
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

    fn process_top_level_query<T: AstInfo>(mut self, query: &Query<T>) -> Result<(), String> {
        let top_box = self.process_query(query, None)?;
        self.model.top_box = top_box;
        Ok(())
    }

    fn process_query<T: AstInfo>(
        &mut self,
        query: &Query<T>,
        parent_context: Option<&NameResolutionContext>,
    ) -> Result<BoxId, String> {
        let box_id = self.model.make_select_box();
        let mut current_context = NameResolutionContext::new(box_id, parent_context);
        self.add_ctes_to_context(&query.ctes, &mut current_context)?;
        self.process_query_body(&query.body, box_id, &mut current_context)?;
        // @todo order by, limit, offset
        Ok(box_id)
    }

    fn add_ctes_to_context<T: AstInfo>(
        &mut self,
        ctes: &Vec<Cte<T>>,
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

    fn process_query_body<T: AstInfo>(
        &mut self,
        body: &SetExpr<T>,
        query_box: BoxId,
        context: &mut NameResolutionContext,
    ) -> Result<(), String> {
        match body {
            SetExpr::Select(select) => self.process_select(&*select, query_box, context),
            _ => Err(format!("@todo unsupported stuff")),
        }
    }

    fn process_select<T: AstInfo>(
        &mut self,
        select: &sql_parser::ast::Select<T>,
        query_box: BoxId,
        context: &mut NameResolutionContext,
    ) -> Result<(), String> {
        self.process_from_clause(&select.from, query_box, context)?;
        // @todo selection, grouping, having, projection, distinct
        Ok(())
    }

    fn process_from_clause<T: AstInfo>(
        &mut self,
        from: &Vec<TableWithJoins<T>>,
        query_box: BoxId,
        context: &mut NameResolutionContext,
    ) -> Result<(), String> {
        Ok(())
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
