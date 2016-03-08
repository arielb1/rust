// Copyright 2016 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use rustc::mir::repr::*;

/// Return the set of blocks that have a single inedge
pub fn single_source_blocks(mir: &Mir) -> BasicBlockSet {
    let mut seen = BasicBlockSet::new(mir);
    let mut result = BasicBlockSet::new(mir);

    let mut worklist = vec![];

    let visit = |worklist, b| {
        if seen.insert(b) {
            worklist.push(b);
            result.insert(b);
        } else {
            // already visited that block - it has multile this is
            result.remove(b);
        }
    };

    seen.insert(START_BLOCK);
    result.insert(START_BLOCK);

    let mut worklist = vec![START_BLOCK];
    while let Some(bb) = worklist.pop() {
        for &succ in mir.basic_block_data(bb).terminator().successors().iter() {
            if seen.insert(succ) {
                worklist.push(succ);
            }
        }
    }

    result
}

/// Mass removal of basic blocks to keep the ID-remapping cheap.
pub fn retain_basic_blocks(mir: &mut Mir, keep: &BasicBlockSet) {
    let num_blocks = mir.basic_blocks.len();

    let mut replacements: Vec<_> = (0..num_blocks).map(BasicBlock::new).collect();
    let mut used_blocks = 0;
    for alive_index in keep.iter() {
        replacements[alive_index] = BasicBlock::new(used_blocks);
        if alive_index != used_blocks {
            // Swap the next alive block data with the current available slot. Since alive_index is
            // non-decreasing this is a valid operation.
            mir.basic_blocks.swap(alive_index, used_blocks);
        }
        used_blocks += 1;
    }
    mir.basic_blocks.truncate(used_blocks);

    for bb in mir.all_basic_blocks() {
        for target in mir.basic_block_data_mut(bb).terminator_mut().successors_mut() {
            *target = replacements[target.index()];
        }
    }
}
