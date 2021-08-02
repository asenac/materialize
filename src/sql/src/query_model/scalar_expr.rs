// Copyright Materialize, Inc. and contributors. All rights reserved.
//
// Use of this software is governed by the Business Source License
// included in the LICENSE file.
//
// As of the Change Date specified in that file, in accordance with
// the Business Source License, use of this software will be governed
// by the Apache License, Version 2.0.

use expr::{AggregateFunc, BinaryFunc, VariadicFunc};
use std::cell::Ref;
use std::collections::HashSet;
use std::fmt;

use crate::query_model::{Model, QuantifierId, QuantifierSet, QueryBox};

#[derive(Debug, PartialEq, Clone)]
pub enum Expr {
    ColumnReference(ColumnReference),
    BaseColumn(BaseColumn),
    CallBinary {
        func: BinaryFunc,
        expr1: Box<Expr>,
        expr2: Box<Expr>,
    },
    CallVariadic {
        func: VariadicFunc,
        exprs: Vec<Expr>,
    },
    CallAggregate {
        /// Names the aggregation function.
        func: AggregateFunc,
        /// An expression which extracts from each row the input to `func`.
        expr: Box<Expr>,
        /// Should the aggregation be applied only to distinct results in each group.
        distinct: bool,
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
            Expr::CallBinary { func, expr1, expr2 } => {
                if func.is_infix_op() {
                    write!(f, "({} {} {})", expr1, func, expr2)
                } else {
                    write!(f, "{}({}, {})", func, expr1, expr2)
                }
            }
            Expr::CallVariadic { func, exprs } => {
                write!(f, "{}({})", func, ore::str::separated(", ", exprs.clone()))
            }
            Expr::CallAggregate {
                func,
                expr,
                distinct,
            } => {
                write!(
                    f,
                    "{}({}{})",
                    func,
                    if *distinct { "distinct " } else { "" },
                    expr
                )
            }
        }
    }
}

impl Expr {
    // @todo use a generic visit method
    pub fn collect_column_references_from_context(
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
            Expr::CallBinary {
                func: _,
                expr1,
                expr2,
            } => {
                expr1.collect_column_references_from_context(context, column_refs);
                expr2.collect_column_references_from_context(context, column_refs);
            }
            Expr::CallVariadic { func: _, exprs } => {
                for e in exprs.iter() {
                    e.collect_column_references_from_context(context, column_refs);
                }
            }
            Expr::CallAggregate {
                func: _,
                expr,
                distinct: _,
            } => {
                expr.collect_column_references_from_context(context, column_refs);
            }
        }
    }

    pub fn visit_mut<F, E>(&mut self, f: &mut F) -> Result<(), E>
    where
        F: FnMut(&mut Self) -> Result<(), E>,
    {
        f(self)?;
        match self {
            Expr::ColumnReference(_) | Expr::BaseColumn(_) => {}
            Expr::CallBinary {
                func: _,
                expr1,
                expr2,
            } => {
                expr1.visit_mut(f)?;
                expr2.visit_mut(f)?;
            }
            Expr::CallVariadic { func: _, exprs } => {
                for e in exprs.iter_mut() {
                    e.visit_mut(f)?;
                }
            }
            Expr::CallAggregate {
                func: _,
                expr,
                distinct: _,
            } => {
                expr.visit_mut(f)?;
            }
        }
        Ok(())
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct ColumnReference {
    pub quantifier_id: QuantifierId,
    pub position: usize,
}

impl ColumnReference {
    pub fn dereference<'a>(&self, model: &'a Model) -> ColumnRef<'a> {
        let input_box = model.get_quantifier(self.quantifier_id).borrow().input_box;
        let input_box = model.get_box(input_box).borrow();
        ColumnRef {
            query_box: input_box,
            position: self.position,
        }
    }
}

#[derive(Debug)]
pub struct ColumnRef<'a> {
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
pub struct BaseColumn {
    pub position: usize,
}
