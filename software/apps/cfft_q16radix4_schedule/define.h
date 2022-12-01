// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

/* DEFINES */
#define N_CSAMPLES (4096)
#define LOG2 (12)

#define N_RSAMPLES (2 * N_CSAMPLES)
#define N_BANKS (NUM_CORES * 4)

#define ASM       // Use asm_volatile statements
#define BIT_REV 1 // Apply bitreversal permutations

/* Single core implementation. Uncomment XPULP to have xpulpimg extensions
   enabled. N_FFTs determines the number of FFTs that the single-core has to run
   in sequence. */

//#define SINGLE
//#define XPULP
//#define N_BANKS_SINGLE (N_BANKS * ((N_CSAMPLES + N_BANKS - 1) / N_BANKS))
//#define N_FFTs 1

/* Parallel implementation. Uncomment BITREVERSALTABLE to compute the
   permutation addresses on the run. N_FFTs_COL determines the number of FFTs
   run in parallel over different sub-sets of cores in the cluster. N_FFTs_ROW
   determines the number of FFTs run in sequence over a sub-set of cores in the
   cluster. E.g. if N_CSAMPLES is 4096 the FFT is parallelized over 256 cores.
   We therefore fit 4 columns on TeraPool.
   Each sub-set of 256 cores can operate on several FFTs in sequence. */

//#define PARALLEL
//#define BITREVERSALTABLE
//#define N_FFTs_ROW 16
//#define N_FFTs_COL 1
//#define MAX_COL (N_BANKS / (N_CSAMPLES / 4))

#define WU_STRIDE (1)
#define STEP (4)

/* FUNCTIONS */
#define MIN(x, y) (((x) < (y)) ? (x) : (y))
#define MAX(x, y) (((x) < (y)) ? (y) : (x))

dump(reg1, 1);
dump(reg2, 1);
dump(reg3, 1);
