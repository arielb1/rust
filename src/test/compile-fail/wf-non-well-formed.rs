// Copyright 2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// Check that we catch attempts to create non-well-formed types

struct Bad<T:?Sized+'static, U:?Sized> {
    p1: &'static [T], //~ ERROR the trait `core::marker::Sized` is not implemented
    p2: U, //~ ERROR the trait `core::marker::Sized` is not implemented
    p3: u32
}

trait Tr {}

struct S<T: Tr>(T);

fn b1() -> &'static [(u8,fn(&'static [S<()>]))]
{} //~^ ERROR the trait `Tr` is not implemented
fn b2() -> &'static [[i8]]
{} //~^ ERROR the trait `core::marker::Sized` is not implemented
fn b3() -> &'static [[u16]; 2]
{} //~^ ERROR the trait `core::marker::Sized` is not implemented
fn b4() -> &'static ([i16],)
{} //~^ ERROR the trait `core::marker::Sized` is not implemented
fn b5() -> &'static (u32,[i32],u32)
{} //~^ ERROR the trait `core::marker::Sized` is not implemented
fn b6() -> &'static (u32,u32,[i64])
{} //~^ ERROR the trait `core::marker::Sized` is not implemented

fn main() {}
