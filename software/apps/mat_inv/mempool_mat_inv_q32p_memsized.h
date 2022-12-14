// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

/* GAUSS JORDAN INVERSION */

uint32_t volatile pivot_barrier __attribute__((section(".l1")));

int mempool_GJinv_q32p_memsized(int32_t *pSrc, int32_t *pDst, uint32_t n,
                                uint32_t *flag);

int mempool_GJinv_q32p_memsized(int32_t *pSrc, int32_t *pDst, uint32_t n,
                                uint32_t *flag) {

  int32_t volatile *pSrcT1, *pSrcT2; /* Temporary input data matrix pointer */
  int32_t volatile *pDstT1, *pDstT2; /* Temporary output data matrix pointer */
  int32_t *pPivotRowIn; /* Temporary input and output data matrix pointer */
  int32_t *pPRT_in, *pPivotRowDst,
      *pPRT_pDst; /* Temporary input and output data matrix pointer */

  int32_t in = 0;
  int32_t Xchg1, Xchg2, Xchg3, Xchg4;
  int32_t in1, in2, in3, in4;
  int32_t out1, out2, out3, out4;

  uint32_t absolute_core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  uint32_t core_id = absolute_core_id;
  uint32_t i, j, k, l; /* loop counters */
  uint32_t m =
      n; /* M is the number of rows. However, the matirces must be square. */

  /* CREATE THE IDENTITY MATRIX */

  pDstT1 = pDst;
  for (k = core_id * 4; k < m; k += num_cores * 4) {
    for (j = 0; j < n; j++) {
      pDstT1[k * n + j] = (uint32_t)(k == j);
      pDstT1[(k + 1) * n + j] = (uint32_t)((k + 1) == j);
      pDstT1[(k + 2) * n + j] = (uint32_t)((k + 2) == j);
      pDstT1[(k + 3) * n + j] = (uint32_t)((k + 3) == j);
    }
  }
  //    pDstT1 = pDst;
  //    for (i = absolute_core_id * 4; i < n * m; i += num_cores * 4) {
  //        k = i / n;
  //        j = i % n;
  //        pDstT1[k * n + j] = (uint32_t) (k == j);
  //        pDstT1[k * n + j + 1] = (uint32_t) (k == (j + 1));
  //        pDstT1[k * n + j + 2] = (uint32_t) (k == (j + 2));
  //        pDstT1[k * n + j + 3] = (uint32_t) (k == (j + 3));
  //    }
  //    mempool_log_barrier(2, absolute_core_id);

  /* Index modifier to navigate through the columns */
  l = 0U;
  while (l < n) {

    pSrcT1 = pSrc + (l * n);
    pDstT1 = pDst + (l * n);
    in = *pSrcT1;

    /* CHECK IF PIVOT ELEMENT IS ZERO */
    if (absolute_core_id == 0) {
      if (in == 0U) {
        /* Loop over the rows present below */
        for (k = l + 1U; k < m; k++) {
          pSrcT2 = pSrc + (n * k);
          pDstT2 = pDst + (n * k);
          /* EXCHANGE */
          if (*pSrcT2 != 0) {
            /* Loop over colums to the right of the pivot */
            j = 0;
            while (j < 4 * ((n - l) >> 2U)) {
              Xchg1 = pSrcT2[j];
              Xchg2 = pSrcT2[j + 1];
              Xchg3 = pSrcT2[j + 2];
              Xchg4 = pSrcT2[j + 3];
              out1 = pSrcT1[j];
              out2 = pSrcT1[j + 1];
              out3 = pSrcT1[j + 2];
              out4 = pSrcT1[j + 3];
              pSrcT2[j] = out1;
              pSrcT2[j + 1] = out2;
              pSrcT2[j + 2] = out3;
              pSrcT2[j + 3] = out4;
              pSrcT1[j] = Xchg1;
              pSrcT1[j + 1] = Xchg2;
              pSrcT1[j + 2] = Xchg3;
              pSrcT1[j + 3] = Xchg4;
              j += 4;
            }
            while (j < n - l) {
              Xchg1 = pSrcT2[j];
              pSrcT2[j] = pSrcT1[j];
              pSrcT1[j] = Xchg1;
              j++;
            }
            /* Loop over colums */
            j = 0;
            while (j < 4 * (n >> 2U)) {
              Xchg1 = pDstT2[j];
              Xchg2 = pDstT2[j + 1];
              Xchg3 = pDstT2[j + 2];
              Xchg4 = pDstT2[j + 3];
              out1 = pDstT1[j];
              out2 = pDstT1[j + 1];
              out3 = pDstT1[j + 2];
              out4 = pDstT1[j + 3];
              pDstT2[j] = out1;
              pDstT2[j + 1] = out2;
              pDstT2[j + 2] = out3;
              pDstT2[j + 3] = out4;
              pDstT1[j] = Xchg1;
              pDstT1[j + 1] = Xchg2;
              pDstT1[j + 2] = Xchg3;
              pDstT1[j + 3] = Xchg4;
              j += 4;
            }
            while (j < n) {
              Xchg1 = pDstT2[j];
              pDstT2[j] = pDstT1[j];
              pDstT1[j] = Xchg1;
              j++;
            }
            *flag = 1U;
            break;
          }
        }
      }
      /* Update the status if the matrix is singular */
      if ((*flag == 0U) && (in == 0U)) {
        return 1;
      }
    }
    mempool_log_barrier(2, absolute_core_id);

    /* DIVIDE BY THE PIVOT */
    /* Points to the pivot row of input and destination matrices */
    pPivotRowIn = pSrc + (l * n);
    pPivotRowDst = pDst + (l * n);
    /* Temporary pointers to the pivot row pointers */
    pSrcT1 = pPivotRowIn;
    pSrcT2 = pPivotRowDst;
    /* Pivot element of the row */
    in = *pPivotRowIn;
    /* Loop over columns to the right of pivot */
    core_id = absolute_core_id - (((l * n + l) % N_BANKS) >> 2U);
    core_id = core_id > num_cores ? core_id + num_cores : core_id;
    // for (j = core_id * 4; j < 4 * ((n - l) >> 2U); j += num_cores * 4) {
    //    in1 = pSrcT1[j];
    //    in2 = pSrcT1[j + 1];
    //    in3 = pSrcT1[j + 2];
    //    in4 = pSrcT1[j + 3];
    //    out1 = FIX_DIV(in1, in);
    //    out2 = FIX_DIV(in2, in);
    //    out3 = FIX_DIV(in3, in);
    //    out4 = FIX_DIV(in4, in);
    //    pSrcT1[j] = out1;
    //    pSrcT1[j + 1] = out2;
    //    pSrcT1[j + 2] = out3;
    //    pSrcT1[j + 3] = out4;
    //}
    // if (core_id == 0) {
    //    j = 4 * ((n - l) >> 2U);
    //    while (j < n - l) {
    //        in1 = pSrcT1[j];
    //        pSrcT1[j] = FIX_DIV(in1, in);
    //        j++;
    //    }
    //}
    if (core_id == 0) {
      j = 0;
      while (j < 4 - l % 4) {
        in1 = pSrcT1[j];
        pSrcT1[j] = FIX_DIV(in1, in);
        j++;
      }
    } else {
      j = core_id * 4 - l % 4;
      if (j < (n - l)) {
        in1 = pSrcT1[j];
        in2 = pSrcT1[j + 1];
        in3 = pSrcT1[j + 2];
        in4 = pSrcT1[j + 3];
        out1 = FIX_DIV(in1, in);
        out2 = FIX_DIV(in2, in);
        out3 = FIX_DIV(in3, in);
        out4 = FIX_DIV(in4, in);
        pSrcT1[j] = out1;
        pSrcT1[j + 1] = out2;
        pSrcT1[j + 2] = out3;
        pSrcT1[j + 3] = out4;
      }
    }
    /* Loop over columns */
    core_id = absolute_core_id - (((l * n) % N_BANKS) >> 2U);
    core_id = core_id > num_cores ? core_id + num_cores : core_id;
    for (j = core_id * 4; j < 4 * (n >> 2U); j += num_cores * 4) {
      in1 = pSrcT2[j];
      in2 = pSrcT2[j + 1];
      in3 = pSrcT2[j + 2];
      in4 = pSrcT2[j + 3];
      out1 = FIX_DIV(in1, in);
      out2 = FIX_DIV(in2, in);
      out3 = FIX_DIV(in3, in);
      out4 = FIX_DIV(in4, in);
      pSrcT2[j] = out1;
      pSrcT2[j + 1] = out2;
      pSrcT2[j + 2] = out3;
      pSrcT2[j + 3] = out4;
    }
    // if (core_id == (n >> 2U) - 1) {
    //    j = 4 * (n >> 2U);
    //    while (j < n) {
    //        in1 = pSrcT2[j];
    //        pSrcT2[j] = FIX_DIV(in1, in);
    //        j++;
    //    }
    //}
    mempool_log_barrier(2, absolute_core_id);

    /* REPLACE ROWS */
    pSrcT1 = pSrc;
    pSrcT2 = pDst;
    for (k = absolute_core_id / (n >> 2U); k < m; k += num_cores / (n >> 2U)) {
      /* Only the columns to the right of the pivot are to be processed */
      if (k != l) {
        pSrcT1 = pSrc + k * n;
        pSrcT2 = pDst + k * n;
        /* Element of the reference row */
        in = *pSrcT1;
        /* Reference row pointers */
        pPRT_in = pPivotRowIn;
        pPRT_pDst = pPivotRowDst;
        /* Loop over the columns */
        core_id = absolute_core_id % (n >> 2U);
        core_id = core_id - (l >> 2U);
        j = core_id * 4;
        while (j < 4 * ((n - l) >> 2U)) {
          out1 = pPRT_in[j];
          out2 = pPRT_in[j + 1];
          out3 = pPRT_in[j + 2];
          out4 = pPRT_in[j + 3];
          in1 = pSrcT1[j];
          in2 = pSrcT1[j + 1];
          in3 = pSrcT1[j + 2];
          in4 = pSrcT1[j + 3];
          pSrcT1[j] = in1 - FIX_MUL(in, out1);
          pSrcT1[j + 1] = in2 - FIX_MUL(in, out2);
          pSrcT1[j + 2] = in3 - FIX_MUL(in, out3);
          pSrcT1[j + 3] = in4 - FIX_MUL(in, out4);
          j += 4 * (n >> 2U);
        }
        if (core_id == 0) {
          j = 4 * ((n - l) >> 2U);
          while (j < n - l) {
            in1 = pSrcT1[j];
            out1 = pPRT_in[j];
            pSrcT1[j] = in1 - FIX_MUL(in, out1);
            j++;
          }
        }
        /* Loop over the columns */
        core_id = absolute_core_id % (n >> 2U);
        j = core_id * 4;
        while (j < 4 * (n >> 2U)) {
          out1 = pPRT_pDst[j];
          out2 = pPRT_pDst[j + 1];
          out3 = pPRT_pDst[j + 2];
          out4 = pPRT_pDst[j + 3];
          in1 = pSrcT2[j];
          in2 = pSrcT2[j + 1];
          in3 = pSrcT2[j + 2];
          in4 = pSrcT2[j + 3];
          pSrcT2[j] = in1 - FIX_MUL(in, out1);
          pSrcT2[j + 1] = in2 - FIX_MUL(in, out2);
          pSrcT2[j + 2] = in3 - FIX_MUL(in, out3);
          pSrcT2[j + 3] = in4 - FIX_MUL(in, out4);
          j += 4 * (n >> 2U);
        }
        // if (core_id == (n >> 2U) - 1) {
        //    j = 4 * (n >> 2U);
        //    while (j < n) {
        //        in1 = pSrcT2[j];
        //        out1 = pPRT_pDst[j];
        //        pSrcT2[j] = in1 - FIX_MUL(in, out1);
        //        j++;
        //    }
        //}
        // uint32_t core_id_in;
        // uint32_t core_id_Dst;
        // int32_t p1_in, p2_in, p3_in, p4_in;
        // int32_t p1_Dst, p2_Dst, p3_Dst, p4_Dst;
        // core_id_in = absolute_core_id % (n >> 2U) - (l >> 2U);
        // core_id_Dst = absolute_core_id % (n >> 2U);
        // j = core_id_in == 0 ? 0 : (core_id_in * 4 - l % 4);
        // i = core_id_Dst * 4;
        // p1_in = pPRT_in[j];
        // p2_in = pPRT_in[j + 1];
        // p3_in = pPRT_in[j + 2];
        // p4_in = pPRT_in[j + 3];
        // p1_Dst = pPRT_pDst[i];
        // p2_Dst = pPRT_pDst[i + 1];
        // p3_Dst = pPRT_pDst[i + 2];
        // p4_Dst = pPRT_pDst[i + 3];
        // if(core_id_in == 0) {
        //    switch (4 - l % 4) {
        //        case (1):
        //            in1 = pSrcT1[j];
        //            pSrcT1[j] = in1 - FIX_MUL(in, p1_in);
        //            break;
        //        case (2):
        //            in1 = pSrcT1[j];
        //            in2 = pSrcT1[j + 1];
        //            pSrcT1[j] = in1 - FIX_MUL(in, p1_in);
        //            pSrcT1[j + 1] = in2 - FIX_MUL(in, p2_in);
        //            break;
        //        case (3):
        //            in1 = pSrcT1[j];
        //            in2 = pSrcT1[j + 1];
        //            in3 = pSrcT1[j + 2];
        //            pSrcT1[j] = in1 - FIX_MUL(in, p1_in);
        //            pSrcT1[j + 1] = in2 - FIX_MUL(in, p2_in);
        //            pSrcT1[j + 2] = in3 - FIX_MUL(in, p3_in);
        //            break;
        //        case (4):
        //            in1 = pSrcT1[j];
        //            in2 = pSrcT1[j + 1];
        //            in3 = pSrcT1[j + 2];
        //            in4 = pSrcT1[j + 3];
        //            pSrcT1[j] = in1 - FIX_MUL(in, p1_in);
        //            pSrcT1[j + 1] = in2 - FIX_MUL(in, p2_in);
        //            pSrcT1[j + 2] = in3 - FIX_MUL(in, p3_in);
        //            pSrcT1[j + 3] = in4 - FIX_MUL(in, p4_in);
        //            break;
        //    }
        //} else {
        //    in1 = pSrcT1[j];
        //    in2 = pSrcT1[j + 1];
        //    in3 = pSrcT1[j + 2];
        //    in4 = pSrcT1[j + 3];
        //    pSrcT1[j] = in1 - FIX_MUL(in, p1_in);
        //    pSrcT1[j + 1] = in2 - FIX_MUL(in, p2_in);
        //    pSrcT1[j + 2] = in3 - FIX_MUL(in, p3_in);
        //    pSrcT1[j + 3] = in4 - FIX_MUL(in, p4_in);
        //}
        // in1 = pSrcT2[i];
        // in2 = pSrcT2[i + 1];
        // in3 = pSrcT2[i + 2];
        // in4 = pSrcT2[i + 3];
        // pSrcT2[i]     = in1 - FIX_MUL(in, p1_Dst);
        // pSrcT2[i + 1] = in2 - FIX_MUL(in, p2_Dst);
        // pSrcT2[i + 2] = in3 - FIX_MUL(in, p3_Dst);
        // pSrcT2[i + 3] = in4 - FIX_MUL(in, p4_Dst);
      }
    }
    mempool_log_barrier(2, absolute_core_id);

    //        /* REPLACE ROWS */
    //        pSrcT1 = pSrc;
    //        pSrcT2 = pDst;
    //        /* Reference row pointers */
    //        pPRT_in = pSrc + (l * n);
    //        pPRT_pDst = pDst + (l * n);
    //        int32_t pivot = *pPRT_in;
    //        uint32_t nPE = (n >> 2U);
    //        uint32_t check = 0;
    //        if (absolute_core_id >= m * nPE)
    //            mempool_wfi();
    //        for (k = absolute_core_id / nPE; k < m; k += num_cores / nPE) {
    //            /* Only the columns to the right of the pivot are to be
    //            processed */ if (k != l) {
    //                pSrcT1 = pSrc + k * n;
    //                pSrcT2 = pDst + k * n;
    //                /* Element of the reference row */
    //                in = *pSrcT1;
    //                /* Loop over the columns */
    //                core_id = absolute_core_id % nPE;
    //                core_id = core_id - (l >> 2U);
    //                j = core_id * 4;
    //                while (j < 4 * ((n - l) >> 2U)) {
    //                    out1 = pPRT_in[j];
    //                    out2 = pPRT_in[j + 1];
    //                    out3 = pPRT_in[j + 2];
    //                    out4 = pPRT_in[j + 3];
    //                    out1 = FIX_DIV(out1, pivot);
    //                    out2 = FIX_DIV(out2, pivot);
    //                    out3 = FIX_DIV(out3, pivot);
    //                    out4 = FIX_DIV(out4, pivot);
    //                    in1 = pSrcT1[j];
    //                    in2 = pSrcT1[j + 1];
    //                    in3 = pSrcT1[j + 2];
    //                    in4 = pSrcT1[j + 3];
    //                    pSrcT1[j] = in1 - FIX_MUL(in, out1);
    //                    pSrcT1[j + 1] = in2 - FIX_MUL(in, out2);
    //                    pSrcT1[j + 2] = in3 - FIX_MUL(in, out3);
    //                    pSrcT1[j + 3] = in4 - FIX_MUL(in, out4);
    //                    j += 4 * (n >> 2U);
    //                }
    //                if (core_id == 0) {
    //                    j = 4 * ((n - l) >> 2U);
    //                    while (j < n - l) {
    //                        out1 = pPRT_in[j];
    //                        out1 = FIX_DIV(out1, pivot);
    //                        in1 = pSrcT1[j];
    //                        pSrcT1[j] = in1 - FIX_MUL(in, out1);
    //                        j++;
    //                    }
    //                }
    //                /* Loop over the columns */
    //                core_id = absolute_core_id % nPE;
    //                j = core_id * 4;
    //                while (j < 4 * (n >> 2U)) {
    //                    out1 = pPRT_pDst[j];
    //                    out2 = pPRT_pDst[j + 1];
    //                    out3 = pPRT_pDst[j + 2];
    //                    out4 = pPRT_pDst[j + 3];
    //                    out1 = FIX_DIV(out1, pivot);
    //                    out2 = FIX_DIV(out2, pivot);
    //                    out3 = FIX_DIV(out3, pivot);
    //                    out4 = FIX_DIV(out4, pivot);
    //                    in1 = pSrcT2[j];
    //                    in2 = pSrcT2[j + 1];
    //                    in3 = pSrcT2[j + 2];
    //                    in4 = pSrcT2[j + 3];
    //                    pSrcT2[j]     = in1 - FIX_MUL(in, out1);
    //                    pSrcT2[j + 1] = in2 - FIX_MUL(in, out2);
    //                    pSrcT2[j + 2] = in3 - FIX_MUL(in, out3);
    //                    pSrcT2[j + 3] = in4 - FIX_MUL(in, out4);
    //                    j += 4 * nPE;
    //                }
    //                __atomic_fetch_add(&pivot_barrier, 1, __ATOMIC_RELAXED);
    //                mempool_wfi();
    //            } else {
    //                do {
    //                    check = __atomic_fetch_add(&pivot_barrier, 0,
    //                    __ATOMIC_RELAXED); mempool_wait(20);
    //                } while (check < ((m - 1) * nPE));
    //                /* Loop over the columns */
    //                core_id = absolute_core_id % (n >> 2U);
    //                core_id = core_id - (l >> 2U);
    //                j = core_id * 4;
    //                while (j < 4 * ((n - l) >> 2U)) {
    //                    in1 = pPRT_in[j];
    //                    in2 = pPRT_in[j + 1];
    //                    in3 = pPRT_in[j + 2];
    //                    in4 = pPRT_in[j + 3];
    //                    out1 = FIX_DIV(in1, pivot);
    //                    out2 = FIX_DIV(in2, pivot);
    //                    out3 = FIX_DIV(in3, pivot);
    //                    out4 = FIX_DIV(in4, pivot);
    //                    pPRT_in[j] = out1;
    //                    pPRT_in[j + 1] = out2;
    //                    pPRT_in[j + 2] = out3;
    //                    pPRT_in[j + 3] = out4;
    //                    j += 4 * (n >> 2U);
    //                }
    //                if (core_id == 0) {
    //                    j = 4 * ((n - l) >> 2U);
    //                    while (j < n - l) {
    //                        in1 = pPRT_in[j];
    //                        pPRT_in[j] = FIX_DIV(in1, pivot);
    //                        j++;
    //                    }
    //                }
    //                /* Loop over the columns */
    //                core_id = absolute_core_id % (n >> 2U);
    //                j = core_id * 4;
    //                while (j < 4 * (n >> 2U)) {
    //                    in1 = pPRT_pDst[j];
    //                    in2 = pPRT_pDst[j + 1];
    //                    in3 = pPRT_pDst[j + 2];
    //                    in4 = pPRT_pDst[j + 3];
    //                    out1 = FIX_DIV(in1, pivot);
    //                    out2 = FIX_DIV(in2, pivot);
    //                    out3 = FIX_DIV(in3, pivot);
    //                    out4 = FIX_DIV(in4, pivot);
    //                    pPRT_pDst[j] = out1;
    //                    pPRT_pDst[j + 1] = out2;
    //                    pPRT_pDst[j + 2] = out3;
    //                    pPRT_pDst[j + 3] = out4;
    //                    j += 4 * (n >> 2U);
    //                }
    //                if (core_id == (n >> 2U) - 1) {
    //                    j = 4 * (n >> 2U);
    //                    while (j < n) {
    //                        in1 = pPRT_pDst[j];
    //                        pPRT_pDst[j] = FIX_DIV(in1, pivot);
    //                        j++;
    //                    }
    //                }
    //                if ((m * nPE) - 1 == __atomic_fetch_add(&pivot_barrier, 1,
    //                __ATOMIC_RELAXED)) {
    //                    __atomic_store_n(&pivot_barrier, 0, __ATOMIC_RELAXED);
    //                    __sync_synchronize();
    //                    wake_up_all();
    //                }
    //                mempool_wfi();
    //            }
    //        }

    //        /* REPLACE ROWS */
    //        pSrcT1 = pSrc;
    //        pSrcT2 = pDst;
    //        for (i = absolute_core_id * 4; i < (n * m); i += num_cores * 4) {
    //            k = i / n;
    //            if (k != l) {
    //                in = *(pSrc + k * n);
    //                j = i - (k * n);
    //                if (j >= 4 * (l >> 2U)) {
    //                    if (j == 4 * (l >> 2U)) {
    //                        pSrcT1 = pSrc + k * n;
    //                        pPRT_in = pPivotRowIn;
    //                        uint32_t bound = j + 4 - l;
    //                        j = 0;
    //                        while (j < bound) {
    //                            in1 = *pSrcT1;
    //                            out1 = *pPRT_in++;
    //                            *pSrcT1++ = in1 - FIX_MUL(in, out1);
    //                            j++;
    //                        }
    //                    } else {
    //                        pSrcT1 = pSrc + (i - l);
    //                        pPRT_in = pPivotRowIn + (j - l);
    //                        in1 = *pSrcT1;
    //                        in2 = *(pSrcT1 + 1);
    //                        in3 = *(pSrcT1 + 2);
    //                        in4 = *(pSrcT1 + 3);
    //                        out1 = *pPRT_in++;
    //                        out2 = *pPRT_in++;
    //                        out3 = *pPRT_in++;
    //                        out4 = *pPRT_in++;
    //                        *pSrcT1++ = in1 - FIX_MUL(in, out1);
    //                        *pSrcT1++ = in2 - FIX_MUL(in, out2);
    //                        *pSrcT1++ = in3 - FIX_MUL(in, out3);
    //                        *pSrcT1++ = in4 - FIX_MUL(in, out4);
    //                    }
    //                }
    //                pSrcT2 = pDst + i;
    //                pPRT_pDst = pPivotRowDst + j;
    //                in1 = *pSrcT2;
    //                in2 = *(pSrcT2 + 1);
    //                in3 = *(pSrcT2 + 2);
    //                in4 = *(pSrcT2 + 3);
    //                out1 = *pPRT_pDst++;
    //                out2 = *pPRT_pDst++;
    //                out3 = *pPRT_pDst++;
    //                out4 = *pPRT_pDst++;
    //                *pSrcT2++ = in1 - FIX_MUL(in, out1);
    //                *pSrcT2++ = in2 - FIX_MUL(in, out2);
    //                *pSrcT2++ = in3 - FIX_MUL(in, out3);
    //                *pSrcT2++ = in4 - FIX_MUL(in, out4);
    //            }
    //        }
    //        mempool_log_barrier(2, absolute_core_id);
    //        /* REPLACE ROWS */
    //        pSrcT1 = pSrc;
    //        pSrcT2 = pDst;
    //        core_id = absolute_core_id;
    //        for (k = core_id; k < m; k += num_cores) {
    //            /* Only the columns to the right of the pivot are to be
    //            processed */ if (k != l) {
    //                pSrcT1 = pSrc + k * n;
    //                pSrcT2 = pDst + k * n;
    //                /* Element of the reference row */
    //                in = *pSrcT1;
    //                /* Reference row pointers */
    //                pPRT_in = pPivotRowIn;
    //                pPRT_pDst = pPivotRowDst;
    //                /* Loop over the columns */
    //                j = 0;
    //                while (j < 4 * ((n - l) >> 2U)) {
    //                    in1 = pSrcT1[j];
    //                    in2 = pSrcT1[j + 1];
    //                    in3 = pSrcT1[j + 2];
    //                    in4 = pSrcT1[j + 3];
    //                    out1 = pPRT_in[j];
    //                    out2 = pPRT_in[j + 1];
    //                    out3 = pPRT_in[j + 2];
    //                    out4 = pPRT_in[j + 3];
    //                    pSrcT1[j] = in1 - FIX_MUL(in, out1);
    //                    pSrcT1[j + 1] = in2 - FIX_MUL(in, out2);
    //                    pSrcT1[j + 2] = in3 - FIX_MUL(in, out3);
    //                    pSrcT1[j + 3] = in4 - FIX_MUL(in, out4);
    //                    j += 4;
    //                }
    //                while (j < n - l) {
    //                    in1 = pSrcT1[j];
    //                    out1 = pPRT_in[j];
    //                    pSrcT1[j] = in1 - FIX_MUL(in, out1);
    //                    j++;
    //                }
    //                /* Loop over the columns */
    //                j = 0;
    //                while (j < 4 * (n >> 2U)) {
    //                    in1 = pSrcT2[j];
    //                    in2 = pSrcT2[j + 1];
    //                    in3 = pSrcT2[j + 2];
    //                    in4 = pSrcT2[j + 3];
    //                    out1 = pPRT_pDst[j];
    //                    out2 = pPRT_pDst[j + 1];
    //                    out3 = pPRT_pDst[j + 2];
    //                    out4 = pPRT_pDst[j + 3];
    //                    pSrcT2[j] = in1 - FIX_MUL(in, out1);
    //                    pSrcT2[j + 1] = in2 - FIX_MUL(in, out2);
    //                    pSrcT2[j + 2] = in3 - FIX_MUL(in, out3);
    //                    pSrcT2[j + 3] = in4 - FIX_MUL(in, out4);
    //                    j += 4;
    //                }
    //                while (j < n) {
    //                    in1 = pSrcT2[j];
    //                    out1 = pPRT_pDst[j];
    //                    pSrcT2[j] = in1 - FIX_MUL(in, out1);
    //                    j++;
    //                }
    //            }
    //        }
    //        mempool_log_barrier(2, absolute_core_id);

    pSrc++; /* Increment the input pointer */
    l++;    /* Increment the index modifier */
  }
  mempool_log_barrier(2, absolute_core_id);

  return 0;
}
