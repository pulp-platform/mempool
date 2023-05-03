// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#![no_std]
#![no_main]

extern crate alloc;
extern crate panic_halt;
extern crate riscv;
extern crate rust_rt;

use alloc::format;
use riscv::register::*;
use rust_rt::barrier::{get_core_count, mempool_barrier};
use rust_rt::entry;
use rust_rt::println;

#[entry]
fn main() -> usize {
    let hartid: u32 = mhartid::read().try_into().unwrap();
    let num_cores: u32 = get_core_count();

    for i in 0..num_cores {
        if hartid == i {
            println!("hart id: {}", hartid);
        }
        mempool_barrier(num_cores);
    }

    return 0x4e110;
}
