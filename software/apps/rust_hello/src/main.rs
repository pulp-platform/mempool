// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#![no_std]
#![no_main]

extern crate panic_halt;
extern crate riscv;
extern crate rust_rt;

use riscv::register::*;
use rust_rt::entry;

use rust_rt::{Format::*, *};

#[entry]
fn main() -> usize {
    // let test : &str = "ieie";
    // println!("{}", 10);
    let hartid: u32 = mhartid::read().try_into().unwrap();
    // println!("{}",hartid);
    //print_nr!("hart_id",hartid, Dec);
    let a: u32 = (5 * 7) / 10 * hartid;
    print_nr_only!(0, Format::Dec);
    print_nr_only!(hartid, Format::Dec);

    println!("0");

    return 0x4e110;
}
