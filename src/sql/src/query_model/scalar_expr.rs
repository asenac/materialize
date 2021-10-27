// Copyright Materialize, Inc. and contributors. All rights reserved.
//
// Use of this software is governed by the Business Source License
// included in the LICENSE file.
//
// As of the Change Date specified in that file, in accordance with
// the Business Source License, use of this software will be governed
// by the Apache License, Version 2.0.

use std::collections::HashSet;
use std::fmt;

use repr::*;

use crate::query_model::{Model, QuantifierId, QuantifierSet};

pub use expr::BinaryFunc;

/// Representation for scalar expressions within a query graph model.
/// Similar to HirScalarExpr but:
/// * subqueries are represented as column references to the subquery
///   quantifiers within the same box the expression belongs to,
/// * aggregate expressions are considered scalar expressions here
///   even though they are only valid in the context of a Grouping box,
/// * column references are represented by a pair (quantifier ID, column
///   position),
/// * BaseColumn is used to represent leaf columns, only allowed in
///   the projection of BaseTables and TableFunctions.
#[derive(Debug, PartialEq, Clone)]
pub enum Expr {
    ColumnReference(ColumnReference),
    BaseColumn(BaseColumn),
    Literal(Row, ColumnType),
    CallBinary {
        func: BinaryFunc,
        expr1: Box<Expr>,
        expr2: Box<Expr>,
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
            Expr::Literal(row, _) => {
                write!(f, "{}", row.unpack_first())
            }
            Expr::CallBinary { func, expr1, expr2 } => {
                if func.is_infix_op() {
                    write!(f, "({} {} {})", expr1, func, expr2)
                } else {
                    write!(f, "{}({}, {})", func, expr1, expr2)
                }
            }
        }
    }
}

impl Expr {
    pub fn visit1<'a, F>(&'a self, mut f: F)
    where
        F: FnMut(&'a Self),
    {
        match self {
            Expr::ColumnReference(_) | Expr::BaseColumn(_) | Expr::Literal(_, _) => (),
            Expr::CallBinary { expr1, expr2, .. } => {
                f(expr1);
                f(expr2);
            }
        }
    }

    pub fn visit<'a, F>(&'a self, f: &mut F)
    where
        F: FnMut(&'a Self),
    {
        self.visit1(|e| e.visit(f));
        f(self);
    }

    pub fn visit1_mut<'a, F>(&'a mut self, mut f: F)
    where
        F: FnMut(&'a mut Self),
    {
        match self {
            Expr::ColumnReference(_) | Expr::BaseColumn(_) | Expr::Literal(_, _) => (),
            Expr::CallBinary { expr1, expr2, .. } => {
                f(expr1);
                f(expr2);
            }
        }
    }

    pub fn visit_mut<F>(&mut self, f: &mut F)
    where
        F: FnMut(&mut Self),
    {
        self.visit1_mut(|e| e.visit_mut(f));
        f(self);
    }

    pub fn column_type(&self, model: &Model) -> repr::ColumnType {
        match &self {
            Expr::ColumnReference(c) => {
                let input_box = model.get_quantifier(c.quantifier_id).borrow().input_box;
                // @todo nullable flag
                model.get_box(input_box).borrow().columns[c.position]
                    .expr
                    .column_type(model)
            }
            Expr::Literal(_, column_type) => column_type.clone(),
            Expr::BaseColumn(base_col) => base_col.column_type.clone(),
            Expr::CallBinary { func, expr1, expr2 } => {
                func.output_type(expr1.column_type(model), expr2.column_type(model))
            }
        }
    }

    pub fn collect_column_references_from_context(
        &self,
        context: &QuantifierSet,
        column_refs: &mut HashSet<ColumnReference>,
    ) {
        self.visit(&mut |e| {
            if let Expr::ColumnReference(c) = e {
                if context.contains(&c.quantifier_id) {
                    column_refs.insert(c.clone());
                }
            }
        });
    }

    /// True if the expression doesn't reference any column from the given set of
    /// quantifiers, even though it may contain other column references from other
    /// contexts.
    pub fn is_constant_within_context(&self, context: &QuantifierSet) -> bool {
        let mut column_refs = HashSet::new();
        self.collect_column_references_from_context(context, &mut column_refs);
        column_refs.is_empty()
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct ColumnReference {
    pub quantifier_id: QuantifierId,
    pub position: usize,
}

#[derive(Debug, PartialEq, Clone)]
pub struct BaseColumn {
    pub position: usize,
    pub column_type: repr::ColumnType,
}
