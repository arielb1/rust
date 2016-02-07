// Copyright 2016 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use std::iter;

use rustc::mir::visit::{Visitor, LvalueContext};
use rustc::mir::repr::*;
use rustc::middle::ty;
use rustc::util::nodemap::FnvHashMap;

use syntax::codemap::DUMMY_SP;

use transform::MirPass;

pub struct DropFlagAnnotator<'a, 'tcx: 'a> {
    // FIXME: run this on monomorphized IR?
    env: &'a ty::ParameterEnvironment<'a, 'tcx>
}

impl<'a, 'tcx> DropFlagAnnotator<'a, 'tcx> {
    pub fn new(env: &'a ty::ParameterEnvironment<'a, 'tcx>) -> Self {
        DropFlagAnnotator {
            env: env
        }
    }
}

impl<'a, 'tcx> MirPass<'tcx> for DropFlagAnnotator<'a, 'tcx> {
    fn run_on_mir(&mut self, mir: &mut Mir<'tcx>) {
        let mut collector = DropTreeCollector::new(self.env, mir);
        collector.visit_mir(mir);
        collector.dump_drop_flags();
    }
}


#[derive(Debug, PartialEq, Eq, Hash)]
pub enum Void {}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum DropBase {
    Var(u32),
    Temp(u32),
    Arg(u32),
    ReturnPointer,
}

pub type DropProjection<'tcx> = ProjectionElem<'tcx, Void>;

fn create_drop_projection<'tcx>(tcx: &ty::ctxt<'tcx>,
                                pi: &LvalueProjection<'tcx>)
                                -> DropProjection<'tcx> {
    match pi.elem {
        ProjectionElem::Deref => ProjectionElem::Deref,
        ProjectionElem::Field(f) => ProjectionElem::Field(f),
        ProjectionElem::ConstantIndex { offset, min_length, from_end } => {
            ProjectionElem::ConstantIndex {
                offset: offset,
                min_length: min_length,
                from_end: from_end
            }
        }
        ProjectionElem::Downcast(adt, vt) => {
            ProjectionElem::Downcast(adt, vt)
        }
        ProjectionElem::Index(ref i) => {
            tcx.sess.bug(&format!("can't move out of array index {:?}", i))
        }
    }
}

struct DropTreeNode<'tcx> {
    drop_flag: Option<u32>,
    children: FnvHashMap<DropProjection<'tcx>, DropTreeNode<'tcx>>
}

impl<'tcx> DropTreeNode<'tcx> {
    fn new() -> Self {
        DropTreeNode {
            drop_flag: None,
            children: FnvHashMap()
        }
    }
}

struct DropTreeCollector<'a, 'tcx: 'a> {
    drop_tree: FnvHashMap<DropBase, DropTreeNode<'tcx>>,
    next_drop_flag: u32,
    env: &'a ty::ParameterEnvironment<'a, 'tcx>,
    mir: &'a Mir<'tcx>
}

impl<'a, 'tcx> DropTreeCollector<'a, 'tcx> {
    fn new(env: &'a ty::ParameterEnvironment<'a, 'tcx>,
           mir: &'a Mir<'tcx>) -> Self {
        DropTreeCollector {
            drop_tree: FnvHashMap(),
            next_drop_flag: 0,
            env: env,
            mir: mir
        }
    }

    fn tcx(&self) -> &'a ty::ctxt<'tcx> {
        self.env.tcx
    }

    fn get_or_create_drop_tree_node(&mut self, lvalue: &Lvalue<'tcx>)
        -> &mut DropTreeNode<'tcx>
    {
        debug!("get_or_create_drop_tree_node({:?})", lvalue);
        let tcx = self.tcx();
        match *lvalue {
            Lvalue::Var(v) => self.base_drop_tree_node(DropBase::Var(v)),
            Lvalue::Temp(t) => self.base_drop_tree_node(DropBase::Temp(t)),
            Lvalue::Arg(a) => self.base_drop_tree_node(DropBase::Arg(a)),
            Lvalue::ReturnPointer => {
                self.base_drop_tree_node(DropBase::ReturnPointer)
            }
            Lvalue::Static(s) => {
                tcx.sess.bug(&format!("can't drop static {:?}", s));
            }
            Lvalue::Projection(ref pi) => {
                let base = self.get_or_create_drop_tree_node(&pi.base);
                let pi_elem = create_drop_projection(tcx, pi);
                base.children.entry(pi_elem).or_insert_with(|| {
                    debug!("creating drop tree node for {:?}", lvalue);
                    DropTreeNode::new()
                })
            }
        }
    }

    fn base_drop_tree_node(&mut self, node: DropBase)
                           -> &mut DropTreeNode<'tcx>
    {
        debug!("base_drop_tree_node({:?})", node);
        self.drop_tree.entry(node).or_insert_with(|| {
            debug!("creating drop tree node for {:?}", node);
            DropTreeNode::new()
        })
    }

    fn dump_drop_tree_node(&self, offset: usize, node: &DropTreeNode<'tcx>) {
        let pad: String = iter::repeat(' ').take(offset*2).collect();
        info!("{}drop flag: {:?}", pad, node.drop_flag);
        for (proj, node) in &node.children {
            info!("{}{:?}:", pad, proj);
            self.dump_drop_tree_node(offset+1, node);
        }
    }

    fn dump_drop_flags(&self) {
        info!("drop flag info:");
        for (base, node) in &self.drop_tree {
            info!("  {:?}:", base);
            self.dump_drop_tree_node(2, node);
        }
    }

    fn add_drop_for(&mut self, lvalue: &Lvalue<'tcx>) {
        let ty = self.mir.lvalue_ty(self.tcx(), lvalue).to_ty(self.tcx());
        debug!("add_drop_for({:?}: {:?})", lvalue, ty);
        if !self.tcx().type_needs_drop_given_env(ty, self.env) {
            debug!("add_drop_for({:?}: {:?}) - no dtor, skip", lvalue, ty);
            return;
        }

        // borrowck bypass
        let ix = self.next_drop_flag;
        if ix == !0 { self.tcx().sess.fatal("drop flag overflow") }

        {
            let node = self.get_or_create_drop_tree_node(lvalue);
            if let Some(_) = node.drop_flag {
                return
            }
            node.drop_flag = Some(ix);
        }
        debug!("add_drop_for({:?}: {:?}) - new drop flag #{:?}",
               lvalue, ty, ix);
        self.next_drop_flag += 1;
    }
}

impl<'a, 'tcx> Visitor<'tcx> for DropTreeCollector<'a, 'tcx> {
    fn visit_lvalue(&mut self, lvalue: &Lvalue<'tcx>, context: LvalueContext) {
        match context {
            LvalueContext::Consume | LvalueContext::Drop => {
                self.add_drop_for(lvalue);
            }
            _ => {}
        }
    }
}
