// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#![no_std]
#![no_main]

extern crate panic_halt;
extern crate riscv;
extern crate rust_rt;

#[macro_use]
extern crate alloc;

use alloc::vec::Vec;
use embedded_alloc::Heap;
use riscv::register::*;
use rust_rt::entry;
use rust_rt::*;

#[global_allocator]
static HEAP: Heap = Heap::empty();

extern "C" {
    static mut __heap_start: u8;
    static mut __heap_end: u8;
}

#[entry]
fn main() -> usize {
    //Initializing Heap
    unsafe {
        let heap_start: usize = &__heap_start as *const u8 as usize;
        let heap_end: usize = &__heap_end as *const u8 as usize;

        use core::mem::MaybeUninit;

        let heap_size: usize = heap_end - heap_start;
        const HEAP_SIZE: usize = 3000;

        static mut HEAP_MEM: [MaybeUninit<u8>; HEAP_SIZE] = [MaybeUninit::uninit(); HEAP_SIZE];
        HEAP.init(HEAP_MEM.as_ptr() as usize, HEAP_SIZE);
        println!("Heap start: {}", heap_start);
        println!("Heap end: {}", heap_end);
        println!("Heap size: {}", heap_size);
    }

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
