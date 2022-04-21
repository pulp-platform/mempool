// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#![no_std]
#![no_main]

extern crate panic_halt;
extern crate rust_rt;
extern crate riscv;

use rust_rt::entry;
use riscv::register::*;

#[entry]
fn main() -> usize {
    let hartid : u32 = mhartid::read().try_into().unwrap();

    return hartid + 0x4e110;
}
