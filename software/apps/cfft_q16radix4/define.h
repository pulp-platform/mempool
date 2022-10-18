// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

/* DEFINES */

#define TEST_64

#if defined(TEST_64)
#define N_CSAMPLES (64)
#elif defined(TEST_256)
#define N_CSAMPLES (256)
#elif defined(TEST_1024)
#define N_CSAMPLES (1024)
#elif defined(TEST_4096)
#define N_CSAMPLES (4096)
#endif
#define N_RSAMPLES (2 * N_CSAMPLES)

#define ASM
#define BITREVERSETABLE
#define BIT_REV 1

//#define SINGLE
//#define XPULP
//#define PRINT_SINGLE

//#define PARALLEL
//#define PRINT_PARALLEL

//#define FOLDED
//#define FOLDED_TWIDDLES
//#define PRINT_FOLDED

/* DATA */
#define N_BANKS (1024)
#define N_TWIDDLES (3 * N_CSAMPLES / 4)

dump(ic, 1);
dump(ic_2, 2);
dump(ic_3, 3);

#define MIN(x, y) (((x) < (y)) ? (x) : (y))
#define MAX(x, y) (((x) < (y)) ? (y) : (x))
