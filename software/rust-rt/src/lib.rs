// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#![no_std]

extern crate riscv;
extern crate riscv_rt_macros as macros;

pub use macros::{entry};

pub mod init;
// pub mod println;
