// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

/* DEFINES */

#if defined(TEST_64)
#define N_CSAMPLES (64)
#define LOG2 (6)
#elif defined(TEST_256)
#define N_CSAMPLES (256)
#define LOG2 (8)
#elif defined(TEST_1024)
#define N_CSAMPLES (1024)
#define LOG2 (10)
#elif defined(TEST_4096)
#define N_CSAMPLES (4096)
#define LOG2 (12)
#endif
#define N_RSAMPLES (2 * N_CSAMPLES)

#define ASM             // Use asm_volatile statements
#define BITREVERSETABLE // Use LUTs for botreversal
#define BIT_REV 1       // Apply bitreversal permutations

/* CHOOSE ONE */

/* SINGLE         --> plain single-core
   SINGLE + XPULP --> single-core with XPULP extensions
   PARALLEL       --> trivial parallelization without folding
   FOLDED         --> parallel kernel with folding of input data
   FOLDED + FOLDED_TWIDDLES --> parallel kernel with folding of input data and
   twiddles */

#define SINGLE
#define XPULP
#define PRINT_SINGLE

// #define PARALLEL
// #define PRINT_PARALLEL

// #define FOLDED
// #define FOLDED_TWIDDLES
// #define PRINT_FOLDED

/* DATA */
#define N_BANKS (1024)
#define N_TWIDDLES (3 * N_CSAMPLES / 4)

#define WU_STRIDE (1)
#define STEP (4 * WU_STRIDE)

dump(reg1, 1);
dump(reg2, 2);
dump(reg3, 3);

#define MIN(x, y) (((x) < (y)) ? (x) : (y))
#define MAX(x, y) (((x) < (y)) ? (y) : (x))
#define ABS(x) (((x) < 0) ? (-x) : (x))
