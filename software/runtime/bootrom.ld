/* Copyright 2021 ETH Zurich and University of Bologna. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Author: Samuel Riedel, ETH Zurich */

OUTPUT_ARCH("riscv")
ENTRY(_start)

/* Include the file processed by the preprocessor called arch.ld.c */
INCLUDE arch.ld

SECTIONS {
  .text : {
    *(.text.init)
    *(.text)
  } > rom
}
