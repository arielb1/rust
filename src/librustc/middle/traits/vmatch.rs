// Copyright 2016 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use middle::def_id::{DefId, CRATE_DEF_INDEX};
use middle::subst::{self, Substs};
use middle::ty::{self, TraitRef, Ty};

use rustc_front::hir;

use std::intrinsics::discriminant_value;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Op {
    TypeParam,
    Finish,
    Tuple,
    Ref,
    RefMut,
    Ptr,
    PtrMut,

    Int,
    Uint,
    Float,
    Prim
}

const OP_MAX: usize = 8;
const STACK_MAX: usize = 8;
const DID_MAX: usize = 2;
const PARAM_MAX: usize = 4;
const LIFETIME_MAX: usize = 8;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct Script {
    /// The script itself, padded with "Finish"
    ops: [(Op, u8); OP_MAX],

    /// DefIds used by DefId ops. FIXME: actually implement this.
    dids: [DefId; DID_MAX],

    /// Maps the nth lifetime found to its slot.
    region_map: [u8; LIFETIME_MAX],

    ty_param_count: u8,
    lt_param_count: u8
}

struct UnfinishedScript<'tcx> {
    ops: Vec<(Op, u8)>,
    dids: Vec<DefId>,
    region_map: Vec<u8>,
    stack: Vec<Ty<'tcx>>,

    ty_param_count: u8,
    lt_param_count: u8
}

impl<'tcx> UnfinishedScript<'tcx> {
    fn new(generics: &ty::Generics<'tcx>) -> Result<Self, CompilationFailed> {
        if generics.types.as_slice().len() >= PARAM_MAX {
            info!("compile: type parameter overflow");
            return Err(CompilationFailed);
        }

        if generics.regions.as_slice().len() >= PARAM_MAX {
            info!("compile: region parameter overflow");
            return Err(CompilationFailed);
        }

        Ok(UnfinishedScript {
            ops: vec![],
            dids: vec![],
            region_map: vec![],
            stack: vec![],
            ty_param_count: generics.types.as_slice().len() as u8,
            lt_param_count: generics.regions.as_slice().len() as u8
        })
    }

    fn add_region(&mut self, r: &ty::Region) -> Result<(), CompilationFailed> {
        match r {
            &ty::ReStatic => {
                info!("compile: 'static unsupported");
                Err(CompilationFailed)
            }
            &ty::ReEarlyBound(eb) => {
                assert_eq!(eb.space, subst::TypeSpace);
                assert!((eb.index as usize) < PARAM_MAX);
                self.region_map.push(eb.index as u8);
                Ok(())
            }
            r => panic!("bad region in impl {:?}", r)
        }
    }

    fn add_type(&mut self, ty: Ty<'tcx>) -> Result<(), CompilationFailed> {
        match ty.sty {
            ty::TyParam(ref p) => {
                let index = match p.space {
                    subst::FnSpace => panic!("fn param in impl"),
                    subst::SelfSpace => self.ty_param_count-1,
                    subst::TypeSpace => p.idx as u8
                };
                self.ops.push((Op::TypeParam, index));
                Ok(())
            }
            ty::TyTuple(ref tys) => {
                if tys.len() > 255 {
                    info!("compile: tuple overflow");
                    return Err(CompilationFailed);
                }

                self.ops.push((Op::Tuple, tys.len() as u8));

                self.push_stack(tys)
            }
            ty::TyRawPtr(mt) => {
                self.ops.push((match mt.mutbl {
                    hir::MutMutable => Op::PtrMut,
                    hir::MutImmutable => Op::Ptr
                }, 0));

                self.push_stack(&[mt.ty])
            }
            ty::TyRef(region, mt) => {
                self.ops.push((match mt.mutbl {
                    hir::MutMutable => Op::RefMut,
                    hir::MutImmutable => Op::Ref
                }, 0));

                try!(self.add_region(region));
                self.push_stack(&[mt.ty])
            }
            ty::TyChar | ty::TyBool | ty::TyStr => {
                let discr = unsafe { discriminant_value(&ty.sty) };
                assert!(discr < 256);

                self.ops.push((Op::Prim, discr as u8));
                Ok(())
            }
            ty::TyInt(ref p) => {
                let discr = unsafe { discriminant_value(p) };
                assert!(discr < 256);

                self.ops.push((Op::Int, discr as u8));
                Ok(())
            }
            ty::TyUint(ref p) => {
                let discr = unsafe { discriminant_value(p) };
                assert!(discr < 256);

                self.ops.push((Op::Uint, discr as u8));
                Ok(())
            }
            ty::TyFloat(ref p) => {
                let discr = unsafe { discriminant_value(p) };
                assert!(discr < 256);

                self.ops.push((Op::Float, discr as u8));
                Ok(())
            }
            _ => {
                info!("compile: unsupported type {}", ty);
                Err(CompilationFailed)
            }
        }
    }

    fn add_substs(&mut self, substs: &Substs<'tcx>) -> Result<(), CompilationFailed> {
        for region in substs.regions().as_slice() {
            try!(self.add_region(region));
        }

        try!(self.push_stack(substs.types.as_slice()));

        Ok(())
    }

    fn push_stack(&mut self, new: &[Ty<'tcx>]) -> Result<(), CompilationFailed> {
        if new.len() > STACK_MAX - self.stack.len() {
            info!("compile: stack overflow");
            return Err(CompilationFailed);
        }

        self.stack.extend(new);

        Ok(())
    }

    fn into_script(self) -> Result<Script, CompilationFailed> {
        if self.ops.len() >= OP_MAX {
            info!("compile: op overflow {}", self.ops.len());
            return Err(CompilationFailed);
        }

        if self.dids.len() >= DID_MAX {
            info!("compile: did overflow {}", self.dids.len());
            return Err(CompilationFailed);
        }

        if self.region_map.len() >= LIFETIME_MAX {
            info!("compile: region overflow {}", self.region_map.len());
            return Err(CompilationFailed);
        }

        let mut result = Script {
            ops: [(Op::Finish, 0); OP_MAX],
            dids: [DefId::local(CRATE_DEF_INDEX); DID_MAX],
            region_map: [0; LIFETIME_MAX],

            ty_param_count: self.ty_param_count,
            lt_param_count: self.lt_param_count
        };

        result.ops[..self.ops.len()].clone_from_slice(&self.ops);
        result.dids[..self.dids.len()].clone_from_slice(&self.dids);
        result.region_map[..self.region_map.len()]
            .clone_from_slice(&self.region_map);

        Ok(result)
    }
}

pub struct CompilationFailed;

pub fn compile<'tcx>(generics: &ty::Generics<'tcx>, trait_ref: TraitRef<'tcx>)
    -> Result<Script, CompilationFailed>
{
    info!("compile({:?}, {:?})", generics, trait_ref);

    let mut script = try!(UnfinishedScript::new(generics));
    try!(script.add_substs(trait_ref.substs));

    while let Some(ty) = script.stack.pop() {
        try!(script.add_type(ty));
    }

    let result = try!(script.into_script());
    info!("compile({:?}, {:?}) done: {:?}", generics, trait_ref, result);
    Ok(result)
}
