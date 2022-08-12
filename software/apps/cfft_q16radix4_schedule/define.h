// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

/* DEFINES */
#define N_CSAMPLES 4096
#define N_RSAMPLES (2*N_CSAMPLES)
#define N_BANKS (NUM_CORES * 4)

//#define SINGLE
//#define XPULP
#define PARALLEL

#define BIT_REV 1
#define ASM
//#define BITREVERSALTABLE

#if defined(SINGLE)
  #define N_FFTs 1
  #define N_BANKS_SINGLE (N_BANKS * ((N_CSAMPLES + N_BANKS - 1) / N_BANKS))
  int16_t pSrc16[N_FFTs * 2 * N_BANKS_SINGLE] __attribute__((aligned(N_FFTs * 2 * N_BANKS_SINGLE), section(".l1")));
#endif

#if defined(PARALLEL)
  #define N_FFTs_ROW 1
  #define N_FFTs_COL 4
  #define MAX_COL (N_BANKS / (N_CSAMPLES / 4))
  int16_t pSrc16[N_FFTs_ROW * 8 * N_BANKS] __attribute__((aligned(N_FFTs_ROW * 8 * N_BANKS), section(".l1")));
  int16_t pDst16[N_FFTs_ROW * 8 * N_BANKS] __attribute__((aligned(N_FFTs_ROW * 8 * N_BANKS), section(".l1")));
  int16_t pCoef16_src[8 * N_BANKS] __attribute__((aligned(8 * N_BANKS), section(".l1")));
  int16_t pCoef16_dst[8 * N_BANKS] __attribute__((aligned(8 * N_BANKS), section(".l1")));
#endif

/* FUNCTIONS */
#define MIN(x, y) (((x) < (y)) ? (x) : (y))
#define MAX(x, y) (((x) < (y)) ? (y) : (x))
dump(id, 1);
