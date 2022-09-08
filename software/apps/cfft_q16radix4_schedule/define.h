// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

/* DEFINES */
#define N_CSAMPLES 4096
#define N_RSAMPLES (2*N_CSAMPLES)
#define N_BANKS (NUM_CORES * 4)

#define BIT_REV 1
#define ASM

#define SINGLE
#define XPULP
#define N_BANKS_SINGLE (N_BANKS * ((N_CSAMPLES + N_BANKS - 1) / N_BANKS))
//#define N_FFTs 1

//#define PARALLEL
//#define BITREVERSALTABLE
//#define N_FFTs_ROW 4
//#define N_FFTs_COL 1
//#define MAX_COL (N_BANKS / (N_CSAMPLES / 4))


/* FUNCTIONS */
#define MIN(x, y) (((x) < (y)) ? (x) : (y))
#define MAX(x, y) (((x) < (y)) ? (y) : (x))
dump(id, 1);
