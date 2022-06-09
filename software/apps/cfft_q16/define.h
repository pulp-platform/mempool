// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

/* DEFINES */
#define N_CSAMPLES 128
#define N_RSAMPLES (2*N_CSAMPLES)
#define TEST_128

//#define SINGLE
//#define PRINT_SINGLE
#define XPULP

#define PARALLEL
#define MEMSIZED
//#define PRINT_PARALLEL

/* DATA */
#define N_BANKS (1024)
#define N_TWIDDLES (3 * N_CSAMPLES / 2)
int16_t pSrc[8*N_BANKS] __attribute__((aligned(8*N_BANKS), section(".l1")));
int16_t pDst[8*N_BANKS] __attribute__((aligned(8*N_BANKS), section(".l1")));
int16_t pCoef16_copy[N_TWIDDLES] __attribute__((aligned(N_CSAMPLES), section(".l1")));

dump(ic, 1);
dump(ic_2, 2);
dump(ic_3, 3);

#define MIN(x, y) (((x) < (y)) ? (x) : (y))
#define MAX(x, y) (((x) < (y)) ? (y) : (x))
