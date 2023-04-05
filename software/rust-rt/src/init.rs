// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use alloc::format;
use embedded_alloc::Heap;
use println;

#[export_name = "_start_rust"]
pub unsafe extern "C" fn start_rust() -> u32 {
    #[global_allocator]
    static HEAP: Heap = Heap::empty();

    extern "C" {
        static mut __heap_start: u8;
        static mut __heap_end: u8;
    }

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

        let used = embedded_alloc::Heap::used(&HEAP);
        let free = embedded_alloc::Heap::free(&HEAP);

        println!("used Head: {}", used);
        println!("free Heap: {}", free);
    }

    extern "Rust" {
        fn main() -> u32;
    }

    let result = main();

    return result;
}
