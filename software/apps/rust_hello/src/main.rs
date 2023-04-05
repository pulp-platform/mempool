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
use alloc::vec::Vec;
use riscv::register::*;
use rust_rt::entry;
use rust_rt::{print, println};

#[entry]
fn main() -> usize {
    let mut xs = Vec::new();
    xs.push(1);
    xs.push(3);

    for item in xs {
        println!("vec item: {}", item);
    }

    let hartid: u32 = mhartid::read().try_into().unwrap();
    let a: u32 = (5 * 7) / 10 * hartid;
    println!("hart id * 3.5: {}", a);

    print!("simple print ");
    print!("+ new line \n");

    return 0x4e110;
}
