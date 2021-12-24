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

use ore::str::separated;
use repr::*;

use crate::plan::expr::{BinaryFunc, NullaryFunc, ScalarWindowFunc, UnaryFunc, VariadicFunc};
use crate::query_model::{QuantifierId, QuantifierSet};
use expr::AggregateFunc;

/// Representation for scalar expressions within a query graph model.
///
/// Similar to HirScalarExpr but:
/// * subqueries are represented as column references to the subquery
///   quantifiers within the same box the expression belongs to,
/// * aggregate expressions are considered scalar expressions here
///   even though they are only valid in the context of a Grouping box,
/// * column references are represented by a pair (quantifier ID, column
///   position),
/// * BaseColumn is used to represent leaf columns, only allowed in
///   the projection of BaseTables and TableFunctions.
///
/// Scalar expressions only make sense within the context of a
/// [`crate::query_model::QueryBox`], and hence, their name.
#[derive(Debug, PartialEq, Clone)]
pub enum BoxScalarExpr {
    /// A reference to a column from a quantifier that either lives in
    /// the same box as the expression or is a sibling quantifier of
    /// an ascendent box of the box that contains the expression.
    ColumnReference(ColumnReference),
    /// A leaf column. Only allowed as standalone expressions in the
    /// projection of `BaseTable` and `TableFunction` boxes.
    BaseColumn(BaseColumn),
    /// A literal value.
    /// (A single datum stored as a row, because we can't own a Datum)
    Literal(Row, ColumnType),
    CallNullary(NullaryFunc),
    CallUnary {
        func: UnaryFunc,
        expr: Box<BoxScalarExpr>,
    },
    CallBinary {
        func: BinaryFunc,
        expr1: Box<BoxScalarExpr>,
        expr2: Box<BoxScalarExpr>,
    },
    CallVariadic {
        func: VariadicFunc,
        exprs: Vec<BoxScalarExpr>,
    },
    If {
        cond: Box<BoxScalarExpr>,
        then: Box<BoxScalarExpr>,
        els: Box<BoxScalarExpr>,
    },
    Aggregate {
        /// Names the aggregation function.
        func: AggregateFunc,
        /// An expression which extracts from each row the input to `func`.
        expr: Box<BoxScalarExpr>,
        /// Should the aggregation be applied only to distinct results in each group.
        distinct: bool,
    },
    Windowing(WindowExpr),
}

#[derive(Debug, PartialEq, Eq, Clone, Hash, PartialOrd, Ord)]
pub struct ColumnReference {
    pub quantifier_id: QuantifierId,
    pub position: usize,
}

#[derive(Debug, PartialEq, Clone)]
pub struct BaseColumn {
    pub position: usize,
    pub column_type: repr::ColumnType,
}

#[derive(Debug, Clone, PartialEq)]
/// Represents the invocation of a window function over a partition with an optional
/// order.
pub struct WindowExpr {
    pub func: WindowExprType,
    pub partition: Vec<BoxScalarExpr>,
    pub order_by: Vec<BoxScalarExpr>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum WindowExprType {
    Scalar(ScalarWindowFunc),
}

impl fmt::Display for BoxScalarExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self {
            BoxScalarExpr::ColumnReference(c) => {
                write!(f, "Q{}.C{}", c.quantifier_id, c.position)
            }
            BoxScalarExpr::BaseColumn(c) => {
                write!(f, "C{}", c.position)
            }
            BoxScalarExpr::Literal(row, _) => {
                write!(f, "{}", row.unpack_first())
            }
            BoxScalarExpr::CallNullary(func) => {
                write!(f, "{}()", func)
            }
            BoxScalarExpr::CallUnary { func, expr } => {
                write!(f, "{}({})", func, expr)
            }
            BoxScalarExpr::CallBinary { func, expr1, expr2 } => {
                if func.is_infix_op() {
                    write!(f, "({} {} {})", expr1, func, expr2)
                } else {
                    write!(f, "{}({}, {})", func, expr1, expr2)
                }
            }
            BoxScalarExpr::CallVariadic { func, exprs } => {
                write!(f, "{}({})", func, separated(", ", exprs.clone()))
            }
            BoxScalarExpr::If { cond, then, els } => {
                write!(f, "if {} then {{{}}} else {{{}}}", cond, then, els)
            }
            BoxScalarExpr::Aggregate {
                func,
                expr,
                distinct,
            } => {
                write!(
                    f,
                    "{}({}{})",
                    *func,
                    if *distinct { "distinct " } else { "" },
                    expr
                )
            }
            BoxScalarExpr::Windowing(expr) => {
                match &expr.func {
                    WindowExprType::Scalar(func) => write!(f, "{}()", func)?,
                }
                write!(f, " over (")?;
                for (i, e) in expr.partition.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    e.fmt(f)?;
                }
                write!(f, ")")?;

                if !expr.order_by.is_empty() {
                    write!(f, " order by (")?;
                    for (i, e) in expr.order_by.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        e.fmt(f)?;
                    }
                    write!(f, ")")?;
                }
                Ok(())
            }
        }
    }
}

impl BoxScalarExpr {
    pub fn visit1<'a, F>(&'a self, mut f: F)
    where
        F: FnMut(&'a Self),
    {
        use BoxScalarExpr::*;
        match self {
            ColumnReference(..) | BaseColumn(..) | Literal(..) | CallNullary(..) => (),
            CallUnary { expr, .. } => f(expr),
            CallBinary { expr1, expr2, .. } => {
                f(expr1);
                f(expr2);
            }
            CallVariadic { exprs, .. } => {
                for expr in exprs {
                    f(expr);
                }
            }
            If { cond, then, els } => {
                f(cond);
                f(then);
                f(els);
            }
            Aggregate { expr, .. } => {
                f(expr);
            }
            Windowing(expr) => {
                for expr in expr.partition.iter() {
                    f(expr);
                }
                for expr in expr.order_by.iter() {
                    f(expr);
                }
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
        use BoxScalarExpr::*;
        match self {
            ColumnReference(..) | BaseColumn(..) | Literal(..) | CallNullary(..) => (),
            CallUnary { expr, .. } => f(expr),
            CallBinary { expr1, expr2, .. } => {
                f(expr1);
                f(expr2);
            }
            CallVariadic { exprs, .. } => {
                for expr in exprs {
                    f(expr);
                }
            }
            If { cond, then, els } => {
                f(cond);
                f(then);
                f(els);
            }
            Aggregate { expr, .. } => {
                f(expr);
            }
            Windowing(expr) => {
                for expr in expr.partition.iter_mut() {
                    f(expr);
                }
                for expr in expr.order_by.iter_mut() {
                    f(expr);
                }
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

    /// A generalization of `visit`. The function `pre` runs on a
    /// `BoxScalarExpr` before it runs on any of the child `BoxScalarExpr`s.
    /// The function `post` runs on child `BoxScalarExpr`s first before the
    /// parent. Optionally, `pre` can return which child `BoxScalarExpr`s, if
    /// any, should be visited (default is to visit all children).
    pub fn visit_pre_post<F1, F2>(&self, pre: &mut F1, post: &mut F2)
    where
        F1: FnMut(&Self) -> Option<Vec<&Self>>,
        F2: FnMut(&Self),
    {
        let to_visit = pre(self);
        if let Some(to_visit) = to_visit {
            for e in to_visit {
                e.visit_pre_post(pre, post);
            }
        } else {
            self.visit1(|e| e.visit_pre_post(pre, post));
        }
        post(self);
    }

    pub fn collect_column_references_from_context(
        &self,
        context: &QuantifierSet,
        column_refs: &mut HashSet<ColumnReference>,
    ) {
        self.visit_pre_post(&mut |_| None, &mut |expr| {
            if let BoxScalarExpr::ColumnReference(c) = expr {
                if context.contains(&c.quantifier_id) {
                    column_refs.insert(c.clone());
                }
            }
        })
    }

    /// True if the expression doesn't reference any column from the given set of
    /// quantifiers, even though it may contain other column references from other
    /// contexts.
    pub fn is_constant_within_context(&self, context: &QuantifierSet) -> bool {
        use BoxScalarExpr::*;
        match self {
            Literal(..) => true,
            ColumnReference(c) => !context.contains(&c.quantifier_id),
            CallUnary { expr, .. } => expr.is_constant_within_context(context),
            CallBinary { expr1, expr2, .. } => {
                expr1.is_constant_within_context(context)
                    && expr2.is_constant_within_context(context)
            }
            CallVariadic { exprs, .. } => {
                for expr in exprs {
                    if !expr.is_constant_within_context(context) {
                        return false;
                    }
                }
                true
            }
            If { cond, then, els } => {
                cond.is_constant_within_context(context)
                    && then.is_constant_within_context(context)
                    && els.is_constant_within_context(context)
            }
            Aggregate { .. } | CallNullary(..) | BaseColumn(..) | Windowing(..) => false,
        }
    }
}
