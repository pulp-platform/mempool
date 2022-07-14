// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

/* Single-core dot-product */
void dotp_single (	int32_t* in_a,
        						int32_t* in_b,
        						int32_t* s,
        						uint32_t Len) {

  uint32_t core_id = mempool_get_core_id();
	if(core_id == 0) {

    mempool_start_benchmark();
    // Kernel execution
    register int32_t local_sum = 0;
    int32_t* end = in_a + Len;
    do {
			local_sum += ((*in_a++) * (*in_b++));
		} while(in_a < end);

    *s = local_sum;
    mempool_stop_benchmark();

	}
  mempool_barrier(NUM_CORES);
  //mempool_log_barrier(2, core_id);
}

/* Single-core dot-product unrolled4 */
void dotp_single_unrolled4 (  int32_t* in_a,
                              int32_t* in_b,
                              int32_t* s,
                              uint32_t Len) {

  uint32_t core_id = mempool_get_core_id();
  if(core_id == 0) {

    mempool_start_benchmark();
    uint32_t reminder = Len % 4;
    uint32_t i;

    int32_t a0 = 0, b0 = 0, a1 = 0, b1 = 0, a2 = 0, b2 = 0, a3 = 0, b3 = 0;
    register int32_t local_sum_1 = 0;
    register int32_t local_sum_2 = 0;
    register int32_t local_sum_3 = 0;
    register int32_t local_sum_4 = 0;
    for(i = 0; i < (Len - reminder); i += 4) {

//        asm volatile (
//          "p.lbu   %[a0], 1(%[idx_a]!);"
//          "p.lbu   %[b0], 1(%[idx_b]!);"
//          "p.lbu   %[a1], 1(%[idx_a]!);"
//          "p.lbu   %[b1], 1(%[idx_b]!);"
//          "p.lbu   %[a2], 1(%[idx_a]!);"
//          "p.lbu   %[b2], 1(%[idx_b]!);"
//          "p.lbu   %[a3], 1(%[idx_a]!);"
//          "p.lbu   %[b3], 1(%[idx_b]!);"
//          "p.mac   %[s0], %[a0], %[b0];"
//          "p.mac   %[s1], %[a1], %[b1];"
//          "p.mac   %[s2], %[a2], %[b2];"
//          "p.mac   %[s3], %[a3], %[b3];"
//          : [a0] "+r" (a0), [a1] "+r" (a1), [a2] "+r" (a2), [a3] "+r" (a3),
//            [b0] "+r" (b0), [b1] "+r" (b1), [b2] "+r" (b2), [b3] "+r" (b3),
//            [idx_a] "+r" (in_a), [idx_b] "+r" (in_b),
//            [s0] "+r" (local_sum_1), [s1] "+r" (local_sum_2), [s2] "+r" (local_sum_3), [s3] "+r" (local_sum_4));

        asm volatile (
          "lw   %[a0], 0(%[idx_a]);"
          "lw   %[b0], 0(%[idx_b]);"
          "lw   %[a1], 4(%[idx_a]);"
          "lw   %[b1], 4(%[idx_b]);"
          "lw   %[a2], 8(%[idx_a]);"
          "lw   %[b2], 8(%[idx_b]);"
          "lw   %[a3], 12(%[idx_a]);"
          "lw   %[b3], 12(%[idx_b]);"
          "addi    %[idx_a], %[idx_a], 16;"
          "addi    %[idx_b], %[idx_b], 16;"
          "p.mac   %[s0], %[a0], %[b0];"
          "p.mac   %[s1], %[a1], %[b1];"
          "p.mac   %[s2], %[a2], %[b2];"
          "p.mac   %[s3], %[a3], %[b3];"
          : [a0] "+r" (a0), [a1] "+r" (a1), [a2] "+r" (a2), [a3] "+r" (a3),
            [b0] "+r" (b0), [b1] "+r" (b1), [b2] "+r" (b2), [b3] "+r" (b3),
            [idx_a] "+r" (in_a), [idx_b] "+r" (in_b),
            [s0] "+r" (local_sum_1), [s1] "+r" (local_sum_2), [s2] "+r" (local_sum_3), [s3] "+r" (local_sum_4));

        //a0 = in_a[i];
        //b0 = in_b[i];
        //a1 = in_a[i + 1];
        //b1 = in_b[i + 1];
        //a2 = in_a[i + 2];
        //b2 = in_b[i + 2];
        //a3 = in_a[i + 3];
        //b3 = in_b[i + 3];
        //local_sum_1 += a0 * b0;
        //local_sum_2 += a1 * b1;
        //local_sum_3 += a2 * b2;
        //local_sum_4 += a3 * b3;
    }
    while (i < Len) {
      a0 = in_a[i];
      b0 = in_b[i];
      local_sum_1 += a0 * b0;
      i++;
    }
    // Reduction
    local_sum_1 += local_sum_2;
    local_sum_3 += local_sum_4;
    local_sum_1 += local_sum_3;
    *s = local_sum_1;
    mempool_stop_benchmark();

  }
  mempool_barrier(NUM_CORES);
  //mempool_log_barrier(2, core_id);
}
