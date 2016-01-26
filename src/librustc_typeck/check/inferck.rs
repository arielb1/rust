// Copyright 2016 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// Checks that all type variables are resolved and report an error
// if that is not the case

use middle::def_id::DefId;
use middle::ty::{self, Ty};
use middle::subst;

use util::common::ErrorReoprted;

use syntax::codemap::Span;

use rustc_front::hir;

use super::FnCtxt;

// Order is important here - first variable wins and
// covered errors are not reported.
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum TypeVariableKind<'tcx> {
    Local(ast::Name),
    Substs(subst::ParamSpace, usize),
    Cast,
    Struct,
    Coercion // not sure this can happen
}

/// A type variable that needs resolving
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct TypeVariable<'tcx> {
    kind: TypeVariableKind,
    expr_id: DefId,
    span: Span,
    ty: Ty<'tcx>
}

pub fn check_no_infer_in_expr(fcx: &FnCtxt, e: &hir::Expr)
                              -> Result<(), ErrorReported> {
    let mut icx = InferckCx::new(fcx);
    icx.visit_expr(e);
    icx.visit_upvar_borrow_map();
    icx.visit_closures();
    icx.visit_liberated_fn_sigs();
    icx.report_errors()
}

pub fn check_no_infer_in_fn(fcx: &FnCtxt, blk: &hir::Block)
                            -> Result<(), ErrorReported> {
    let mut icx = InferckCx::new(fcx);
    icx.visit_block(blk);
    icx.visit_upvar_borrow_map();
    icx.visit_closures();
    icx.visit_liberated_fn_sigs();
    icx.report_errors()
}

struct InferckCx<'cx, 'tcx: 'cx> {
    fcx: &'cx FnCtxt<'cx, 'tcx>,
    type_vars: Vec<TypeVariable<'tcx>>
}


impl<'cx, 'tcx> InferckCx<'cx, 'tcx> {
    fn new(fcx: &'cx FnCtxt<'cx, 'tcx>) -> Self {
        InferckCx { fcx: fcx, type_vars: vec![] }
    }

    fn tcx(&self) -> &'cx ty::ctxt<'tcx> {
        self.fcx.tcx()
    }
}

impl<'cx, 'tcx, 'v> Visitor<'v> for WritebackCx<'cx, 'tcx> {
    fn visit_expr(&mut self, e: &hir::Expr) {
        let def_id = self.tcx().map.as_local_def_id(e.id);
        self.fcx.opt_node_ty_substs(e.id, |substs| {
            for (space, ix, ty) in substs.types.iter_enumerated() {
                self.type_vars.push(TypeVariable {
                    span: e.span, def_id: def_id, ty: ty,
                    kind: TypeVariableKind::Substs(space, ix)
                })
            }
        });

        match e.node {
            hir::ExprPath(..) | // determined by substs
            // builders - type determined by internals
            hir::ExprBox(..) | hir::ExprVec(..) | hir::ExprRepeat(..) |
            hir::ExprTup(..) | hir::ExprLit(..) | hir::ExprRange(..) |
            hir::ExprAddrOf(..) |

            // projections - type determined by internals
            hir::ExprCall(..) | hir::ExprField(..) | hir::ExprTupField(..) |

            // method calls - determined by methodmap
            hir::ExprMethodCall(..) | hir::ExprBinary(..) | hir::ExprUnary(..) |
            hir::ExprIndex(..) |

            // controlflow - type is unit/bot
            hir::ExprWhile(..) | hir::ExprLoop(..) | hir::ExprAssign(..) |
            hir::ExprAssignOp(..) | hir::ExprBreak(..) | hir::ExprAgain(..) |
            hir::ExprRet(..) |

            // controlflow - type determined by internals
            hir::ExprIf(..) | hir::ExprMatch(..) | hir::ExprBlock(..)
            => {}

            hir::ExprType(..) | hir::ExprCast(..) => {
                self.type_vars.push(TypeVariable {
                    span: e.span, def_id: def_id, ty: self.fcx.expr_ty(e),
                    kind: TypeVariableKind::Cast
                })
            }

            hir::ExprStruct(..) => {
            }

            hir::ExprClosure(..) => {
            }
        }

        // adjustments (do we need this really?)
        self.visit_node_id(ResolvingExpr(e.span), e.id);
        self.visit_method_map_entry(ResolvingExpr(e.span),
                                    MethodCall::expr(e.id));

        if let hir::ExprClosure(_, ref decl, _) = e.node {
            for input in &decl.inputs {
                self.visit_node_id(ResolvingExpr(e.span), input.id);
            }
        }

        intravisit::walk_expr(self, e);
    }

    fn visit_pat(&mut self, p: &hir::Pat) {
        if self.fcx.writeback_errors.get() {
            return;
        }

        self.visit_node_id(ResolvingPattern(p.span), p.id);

        debug!("Type for pattern binding {} (id {}) resolved to {:?}",
               pat_to_string(p),
               p.id,
               self.tcx().node_id_to_type(p.id));

        intravisit::walk_pat(self, p);
    }
}
