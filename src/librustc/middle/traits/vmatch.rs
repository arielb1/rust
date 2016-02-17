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
use middle::subst::{self, Substs, VecPerParamSpace};
use middle::ty::{self, TraitRef, Ty};

use std::intrinsics::discriminant_value;
use std::mem;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Op {
    TypeParam,
    Finish,
    Tuple,
    Ref,
    Ptr,

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

    ty_param_count: u32,
    lt_param_count: u32,

    trait_region_param_count: u32,
}

struct UnfinishedScript<'tcx> {
    ops: Vec<(Op, u8)>,
    dids: Vec<DefId>,
    region_map: Vec<u8>,
    stack: Vec<Ty<'tcx>>,

    ty_param_count: u32,
    lt_param_count: u32,

    trait_region_param_count: u32,
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
            ty_param_count: generics.types.as_slice().len() as u32,
            lt_param_count: generics.regions.as_slice().len() as u32,
            trait_region_param_count: 0
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
                    subst::SelfSpace => self.ty_param_count as u8 - 1,
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
                let discr = unsafe { discriminant_value(&mt.mutbl) };
                assert!(discr < 256);

                self.ops.push((Op::Ptr, discr as u8));
                self.push_stack(&[mt.ty])
            }
            ty::TyRef(region, mt) => {
                let discr = unsafe { discriminant_value(&mt.mutbl) };
                assert!(discr < 256);

                self.ops.push((Op::Ref, discr as u8));

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
        if self.ops.len() > OP_MAX {
            info!("compile: op overflow {}", self.ops.len());
            return Err(CompilationFailed);
        }

        if self.dids.len() > DID_MAX {
            info!("compile: did overflow {}", self.dids.len());
            return Err(CompilationFailed);
        }

        if self.region_map.len() > LIFETIME_MAX {
            info!("compile: region overflow {}", self.region_map.len());
            return Err(CompilationFailed);
        }

        let mut result = Script {
            ops: [(Op::Finish, 0); OP_MAX],
            dids: [DefId::local(CRATE_DEF_INDEX); DID_MAX],
            region_map: [0; LIFETIME_MAX],

            ty_param_count: self.ty_param_count,
            lt_param_count: self.lt_param_count,
            trait_region_param_count: self.trait_region_param_count
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

#[derive(Clone, Debug)]
pub struct MatchResult<'tcx> {
    pub eq_tys: Vec<(Ty<'tcx>, Ty<'tcx>)>,
    pub eq_regions: Vec<(&'tcx ty::Region, &'tcx ty::Region)>,
    pub substs: Substs<'tcx>
}

struct MatchState<'tcx> {
    eq_tys: Vec<(Ty<'tcx>, Ty<'tcx>)>,
    eq_regions: Vec<(&'tcx ty::Region, &'tcx ty::Region)>,
    result_tys: [Option<Ty<'tcx>>; PARAM_MAX],
    result_lts: [Option<&'tcx ty::Region>; PARAM_MAX],
    stack: [Option<Ty<'tcx>>; STACK_MAX],
    stack_ptr: usize,
    region_ptr: usize
}

pub struct MatchError;

impl Script {
    fn push_region<'tcx>(&self, ms: &mut MatchState<'tcx>, r: &'tcx ty::Region)
    {
        let mut ms = ms;
        let i = self.region_map[ms.region_ptr];
        ms.region_ptr += 1;

        match mem::replace(&mut ms.result_lts[i as usize], Some(r)) {
            Some(old_r) if old_r != r => ms.eq_regions.push((old_r, r)),
            _ => {}
        }
    }

    fn push_types<'tcx>(&self, ms: &mut MatchState<'tcx>, tys: &[Ty<'tcx>])
    {
        let mut ms = ms;
        if tys.len() > STACK_MAX - ms.stack_ptr {
            panic!()
        }
        let mut i = 0;
        while i < tys.len() {
            ms.stack[ms.stack_ptr+i] = Some(tys[i]);
            i += 1;
        }
        ms.stack_ptr += i;
    }

    fn push_type<'tcx>(&self, ms: &mut MatchState<'tcx>, ty: Ty<'tcx>)
    {
        let mut ms = ms;
        ms.stack[ms.stack_ptr] = Some(ty);
        ms.stack_ptr += 1;
    }

    #[inline(never)]
    pub fn match_<'tcx>(&self, substs: &'tcx Substs<'tcx>, tcx: ty::ctxt<'tcx>)
        -> Result<MatchResult<'tcx>, MatchError>
    {
        let mut ms = MatchState {
            eq_tys: Vec::new(),
            eq_regions: Vec::new(),
            result_tys: [None; PARAM_MAX],
            result_lts: [None; PARAM_MAX],
            stack: [None; STACK_MAX],
            stack_ptr: 0,
            region_ptr: 0
        };

        match substs.regions {
            subst::RegionSubsts::ErasedRegions => {
                ms.region_ptr += self.trait_region_param_count as usize;
            }
            subst::RegionSubsts::NonerasedRegions(ref regions) => {
                for region in regions {
                    self.push_region(&mut ms, region);
                }
            }
        }

        self.push_types(&mut ms, substs.types.as_slice());

        try!(self.do_match(&mut ms));

        let result_tys = ms.result_tys[..self.ty_param_count as usize]
            .iter().map(|ty| ty.unwrap()).collect();
        let result_lts = ms.result_lts[..self.lt_param_count as usize]
            .iter().map(|lt| *lt.unwrap_or(tcx.types.re_static)).collect();

        Ok(MatchResult {
            eq_tys: ms.eq_tys,
            eq_regions: ms.eq_regions,
            substs: Substs::new(
                VecPerParamSpace::new_with_self(result_tys),
                VecPerParamSpace::new_types_only(result_lts)
            )
        })
    }

    #[inline(never)]
    fn do_match<'tcx>(&self, ms: &mut MatchState<'tcx>) -> Result<(), MatchError> {
        let mut ms = ms;
        let mut ip = 0;
        while ms.stack_ptr > 0 {
            let (op, arg) = self.ops[ip];
            ip += 1;
            let ty = ms.stack[ms.stack_ptr].unwrap();
            ms.stack_ptr -= 1;

            match (op, &ty.sty) {
                (Op::TypeParam, _) => {
                    match mem::replace(&mut ms.result_tys[arg as usize], Some(ty)) {
                        Some(old_ty) if old_ty != ty => {
                            ms.eq_tys.push((old_ty, ty));
                        }
                        _ => {}
                    }
                }
                (Op::Finish, _) => unreachable!(),
                (Op::Tuple, &ty::TyTuple(ref tys)) if arg as usize == tys.len() => {
                    self.push_types(&mut ms, tys);
                }
                (Op::Ref, &ty::TyRef(region, mt))
                    if arg as u64 == unsafe { discriminant_value(&mt.mutbl) } =>
                {
                    self.push_region(&mut ms, region);
                    self.push_type(&mut ms, mt.ty);
                }
                (Op::Ptr, &ty::TyRawPtr(mt))
                    if arg as u64 == unsafe { discriminant_value(&mt.mutbl) } =>
                {
                    self.push_type(&mut ms, mt.ty);
                }
                (Op::Int, &ty::TyInt(p))
                    if arg as u64 == unsafe { discriminant_value(&p) } => {}
                (Op::Uint, &ty::TyUint(p))
                    if arg as u64 == unsafe { discriminant_value(&p) } => {}
                (Op::Float, &ty::TyFloat(p))
                    if arg as u64 == unsafe { discriminant_value(&p) } => {}
                (Op::Prim, _)
                    if arg as u64 == unsafe { discriminant_value(&ty.sty) } => {}
                _ => {
                    debug!("match failed: ({:?},{:?}) != {:?}", op, arg, ty);
                    return Err(MatchError);
                }
            }
        }
        Ok(())
    }
}
