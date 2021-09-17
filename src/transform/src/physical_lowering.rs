// Copyright Materialize, Inc. and contributors. All rights reserved.
//
// Use of this software is governed by the Business Source License
// included in the LICENSE file.
//
// As of the Change Date specified in that file, in accordance with
// the Business Source License, use of this software will be governed
// by the Apache License, Version 2.0.

use crate::TransformArgs;

use expr::MirRelationExpr;

#[derive(Debug)]
pub struct OuterJoinLowering;

impl crate::Transform for OuterJoinLowering {
    fn transform(
        &self,
        relation: &mut MirRelationExpr,
        _: TransformArgs,
    ) -> Result<(), crate::TransformError> {
        relation.visit_mut(&mut |e| self.action(e));
        Ok(())
    }
}

impl OuterJoinLowering {
    fn action(&self, relation: &mut MirRelationExpr) {
        match relation {
            MirRelationExpr::OuterJoin { .. } => {}
            MirRelationExpr::FullOuterJoin { .. } => {}
            _ => {}
        }
    }
}
