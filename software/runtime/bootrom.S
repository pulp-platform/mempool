// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Samuel Riedel, ETH Zurich

.globl _start
.section .text;
.section .text.init;

_start:
    la      a0, __l2_start // load the address to the entry point
    wfi
    jr      a0
