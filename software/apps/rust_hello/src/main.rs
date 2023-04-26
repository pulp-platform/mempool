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
use rust_rt::barrier::*;
use rust_rt::entry;
use rust_rt::println;

#[entry]
fn main() -> usize {
    //conviniece function for mhartid::read()
    let hartid: u32 = mhartid::read().try_into().unwrap();

    mempool_barrier_init(hartid);

    for i in 0..3 {
        if hartid == i {
            println!("hart id: {}", hartid);
        }
        mempool_barrier(4);
    }

    return 0x4e110;
}
