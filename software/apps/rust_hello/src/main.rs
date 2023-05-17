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
use rust_rt::benchmark::{start_benchmark, stop_benchmark};
use rust_rt::entry;
use rust_rt::mat_mul::*;
use rust_rt::println;

const M: usize = 64;
const N: usize = 32;
const P: usize = 64;

static mut A: [isize; M * N] = [0; M * N];
static mut B: [isize; N * P] = [0; N * P];
static mut C: [isize; M * P] = [0; M * P];

static A_a: isize = 1;
static A_b: isize = 1;
static A_c: isize = -32;
static B_a: isize = 2;
static B_b: isize = 1;
static B_c: isize = 16;

#[entry]
fn main() -> usize {
    let hartid: usize = mhartid::read().try_into().unwrap();
    let num_cores: usize = get_core_count();

    if hartid == 0 {
        println!("initialise")
    }

    unsafe {
        matrix_init_i32(&mut A, M, N, A_a, A_b, A_c, hartid, num_cores);
        matrix_init_i32(&mut B, N, P, B_a, B_b, B_c, hartid, num_cores);
    }
    // if hartid == 0 {
    //     unsafe {
    //         print_matrix_32(&A, M, N);
    //         print_matrix_32(&B, N, P);
    //     }
    // }

    mempool_barrier(num_cores);

    // start_benchmark();

    // unsafe {
    //     mat_mul_unrolled_parallel(&mut A, &mut B, &mut C, M, N, P, hartid, num_cores);
    // }

    // stop_benchmark();

    // mempool_barrier(num_cores);

    start_benchmark();

    unsafe {
        mat_mul_unrolled_parallel_i32(&A, &B, &mut C, M, N, P, hartid, num_cores);
    }

    stop_benchmark();

    // if hartid == 0 {
    //     unsafe {
    //         print_matrix_32(&C, M, P);
    //     }
    // }

    mempool_barrier(num_cores);

    let a: isize;
    unsafe {
        a = verify_matrix_i32(
            &mut C, M, P, N, A_a, A_b, A_c, B_a, B_b, B_c, hartid, num_cores,
        );
    }


    mempool_barrier(num_cores);

    if hartid == 0 {
        println!("matrix verification: {}", a);
    }

    
    mempool_barrier(num_cores);

    return 0x4e110;
}
