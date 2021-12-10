// Copyright Materialize, Inc. and contributors. All rights reserved.
//
// Use of this software is governed by the Business Source License
// included in the LICENSE file.
//
// As of the Change Date specified in that file, in accordance with
// the Business Source License, use of this software will be governed
// by the Apache License, Version 2.0.

use expr::{LetTag, MirRelationExpr};

use crate::TransformArgs;

/// Remove redundant collections of distinct elements from joins.
#[derive(Debug)]
pub struct RedundantRow;

impl crate::Transform for RedundantRow {
    fn transform(
        &self,
        relation: &mut MirRelationExpr,
        _: TransformArgs,
    ) -> Result<(), crate::TransformError> {
        relation.try_visit_mut_pre(&mut |e| self.action(e))
    }
}

impl RedundantRow {
    pub fn action(&self, relation: &mut MirRelationExpr) -> Result<(), crate::TransformError> {
        if let MirRelationExpr::Let {
            id: _,
            value,
            body,
            tag,
        } = relation
        {
            if let MirRelationExpr::Let {
                id: _,
                value: inner_value,
                body: inner_body,
                tag: inner_tag,
            } = &**value
            {
                match (tag, inner_tag) {
                    // @todo for this case we must copy the default value
                    (LetTag::OneRowAtMost, LetTag::EnsuresOneRow)
                    | (LetTag::EnsuresOneRow, LetTag::OneRowAtMost)
                    | (LetTag::EnsuresOneRow, LetTag::EnsuresOneRow) => {
                        *relation = value.take_dangerous();
                    }
                    _ => {}
                }
            }
        }
        Ok(())
    }
}
