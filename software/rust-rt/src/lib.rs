// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#![no_std]

extern crate embedded_alloc;
extern crate riscv;
extern crate riscv_rt_macros as macros;

extern crate alloc;

pub use macros::entry;

use core::sync::atomic::AtomicU32;

pub mod barrier;
pub mod benchmark;
pub mod init;
pub mod mat_mul;
pub mod println;

pub static BARRIER: AtomicU32 = AtomicU32::new(0);
