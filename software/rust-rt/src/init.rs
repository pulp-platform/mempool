// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#[export_name = "_start_rust"]
pub unsafe extern "C" fn start_rust() -> u32 {
  extern "Rust" {
    fn main() -> u32;
  }

  let result = main();

  return result;
}
