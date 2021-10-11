// Copyright Materialize, Inc. and contributors. All rights reserved.
//
// Use of this software is governed by the Business Source License
// included in the LICENSE file.
//
// As of the Change Date specified in that file, in accordance with
// the Business Source License, use of this software will be governed
// by the Apache License, Version 2.0.

//! Framework for rewriting expressions.

use std::cell::RefCell;

/// Trait that must be implemented for every expression type that supports
/// being transformed by this transform framework.
pub trait VisitMutExpr {
    fn visit_mut_pre_post_in<FnPre, FnPost, FnIn>(
        &mut self,
        pre: &mut FnPre,
        f_in: &mut FnIn,
        post: &mut FnPost,
    ) where
        FnPre: FnMut(&mut Self),
        FnIn: FnMut(&Self, usize),
        FnPost: FnMut(&mut Self);
}

/// Trait for visitors that perform mutation actions during a traversal of
/// the visitable expression.
///
/// `Data` contains the context information of the visitor.
pub trait MutExprVisitor<Expr: VisitMutExpr, Data: Default> {
    /// Invoked when entering the scope of the given expression.
    fn pre_visit(&self, _expr: &mut Expr, _data: &mut Data) {}

    /// Invoked after leaving the scope of a child expression and before entering
    /// the scope of the next child expression. Receives the index of the next
    /// child expression to be visited.
    fn in_visit(&self, _expr: &Expr, _input_idx: usize, _data: &mut Data) {}

    /// Invoked when leaving the scope of the given expression.
    fn post_visit(&self, _expr: &mut Expr, _data: &mut Data) {}
}

/// A list of transformations, represented as `MutExprVisitor`, that can be
/// applied during the same graph traversal. They all must accept the same
/// data type.
struct Transforms<Expr, Data>
where
    Data: Default,
    Expr: VisitMutExpr,
{
    transforms: Vec<Box<dyn MutExprVisitor<Expr, Data>>>,
}

impl<Expr, Data> Transforms<Expr, Data>
where
    Data: Default,
    Expr: VisitMutExpr,
{
    /// Apply the list of tranformations to the given expression.
    fn apply(&self, expr: &mut Expr) {
        let data = RefCell::new(Default::default());
        expr.visit_mut_pre_post_in(
            &mut |e| {
                for t in self.transforms.iter() {
                    t.pre_visit(e, &mut data.borrow_mut());
                }
            },
            &mut |e, input_idx| {
                for t in self.transforms.iter() {
                    t.in_visit(e, input_idx, &mut data.borrow_mut());
                }
            },
            &mut |e| {
                for t in self.transforms.iter() {
                    t.post_visit(e, &mut data.borrow_mut());
                }
            },
        );
    }
}
