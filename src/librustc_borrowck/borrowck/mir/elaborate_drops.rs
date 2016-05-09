// Copyright 2016 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use super::gather_moves::MoveData;
use super::dataflow::{MaybeInitializedLvals, MaybeUninitializedLvals};

use rustc::ty::TyCtxt;
use rustc::mir::repr::*;
use rustc::mir::transform::{Pass, MirPass};
use syntax::ast::NodeId;

pub struct ElaborateDrops;

impl<'tcx> MirPass<'tcx> for ElaborateDrops {
    fn run_pass(&mut self, tcx: &TyCtxt<'tcx>, id: NodeId, mir: &mut Mir<'tcx>) {
        {
            let mir = &*mir;
            let move_data = MoveData::gather_moves(mir, tcx);
            let ((_, _, move_data), flow_inits) =
                super::do_dataflow(tcx, mir, id, &[], (tcx, mir, move_data),
                                   MaybeInitializedLvals::default());
            let (move_data, flow_uninits) =
                super::do_dataflow(tcx, mir, id, &[], move_data,
                                   MaybeUninitializedLvals::default());

            ElaborateDropsCtxt {
                tcx: tcx,
                move_data: move_data
            }
        }.elaborate_drops(mir);
    }
}

impl Pass for ElaborateDrops {}

struct ElaborateDropsCtxt<'a, 'tcx: 'a> {
    tcx: &'a TyCtxt<'tcx>,
    move_data: MoveData<'tcx>,
}

impl<'a, 'tcx> ElaborateDropsCtxt<'a, 'tcx> {
    fn elaborate_drops(&mut self, mir: &mut Mir<'tcx>)
    {
    }
}
