// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#include <stdint.h>
#include <string.h>
#include "math.h"
#include "define.h"

/*******************************************************/
/**                    SINGLE-CORE                    **/
/*******************************************************/

/* Single-core dot-product */
void dotp_single (	int32_t* in_a,
						int32_t* in_b, 
						int32_t* s, 
						uint32_t N_vect, 
						uint32_t id) {

	if(id == 0) {

    mempool_start_benchmark();
    // Kernel execution
    /*int32_t local_sum = 0;
    int32_t* end = in_a + N_vect;
    do {
      int32_t a_tmp, b_tmp;
      asm volatile(
        "p.lbu %[a], 1(%[addrA]!);"
        "p.lbu %[b], 1(%[addrB]!);"
        "p.mac %[c], %[a], %[b];"
        : [c] "+r" (local_sum),
          [addrA] "+r" (in_a), [addrB] "+r" (in_b), [a] "=r" (a_tmp), [b] "=r" (b_tmp));
    } while(in_a<end);
    *s = local_sum;*/
    int32_t local_sum = 0;
    int32_t* end = in_a + N_vect;
		//for(uint32_t i = 0; i < N_vect; i++)
    do {
			local_sum += ((*in_a++)*(*in_b++));
		} while(in_a<end);

    *s = local_sum;
    mempool_stop_benchmark();

	}
  //mempool_barrier(NUM_CORES); // wait until all cores have finished
  mempool_log_barrier(2, id);
}

/* Single-core dot-product unrolled2 */
void dotp_single_unrolled2 ( int32_t* in_a,
                             int32_t* in_b,
                             int32_t* s,
                             uint32_t N_vect,
                             uint32_t id) {
  if(id == 0) {
    int32_t local_sum_1 = 0;
    int32_t local_sum_2 = 0;
    int32_t* end = in_a + ((N_vect>>1)<<1);
    int32_t* end_reminder = in_a + N_vect;

    // Kernel execution
    /*do {

      int32_t a1_tmp, b1_tmp;
      int32_t a2_tmp, b2_tmp;

      asm volatile(
        "p.lbu %[a1], 1(%[addrA]!);"
        "p.lbu %[b1], 1(%[addrB]!);"
        "p.lbu %[a2], 1(%[addrA]!);"
        "p.lbu %[b2], 1(%[addrB]!);"
        "p.mac %[c1], %[a1], %[b1];"
        "p.mac %[c2], %[a2], %[b2];"
        : [c1] "+r" (local_sum_1), [c2] "+r" (local_sum_2),
          [addrA] "+r" (in_a), [addrB] "+r" (in_b),
          [a1] "=r" (a1_tmp), [b1] "=r" (b1_tmp),
          [a2] "=r" (a2_tmp), [b2] "=r" (b2_tmp));

    } while(in_a<end);*/

    //for(uint32_t i = 0; i < N_vect; i++)
    do {
      local_sum_1 += ((*in_a++)*(*in_b++));
      local_sum_2 += ((*in_a++)*(*in_b++));
    } while(in_a<end);

    do {
      local_sum_1 += ((*in_a++)*(*in_b++));
    } while(in_a<end_reminder);

    // Reduction
    local_sum_1 += local_sum_2;
    *s = local_sum_1;

  }
  //mempool_barrier(NUM_CORES); // wait until all cores have finished
  mempool_log_barrier(2, id);
}

/* Single-core dot-product unrolled4 */
void dotp_single_unrolled4 ( int32_t* in_a,
                            int32_t* in_b,
                            int32_t* s,
                            uint32_t N_vect,
                            uint32_t id) {
  if(id == 0) {
    mempool_start_benchmark();
    int32_t local_sum_1 = 0;
    int32_t local_sum_2 = 0;
    int32_t local_sum_3 = 0;
    int32_t local_sum_4 = 0;
    int32_t* end = in_a + ((N_vect>>2)<<2);
    int32_t* end_reminder = in_a + N_vect;

    /*int32_t a1_tmp=0, b1_tmp=0;
    int32_t a2_tmp=0, b2_tmp=0;
    int32_t a3_tmp=0, b3_tmp=0;
    int32_t a4_tmp=0, b4_tmp=0;

    // Kernel execution
    while(in_a<end) {
      asm volatile(
        "p.lbu %[a1], 1(%[addrA]!);"
        "p.lbu %[b1], 1(%[addrB]!);"
        "p.lbu %[a2], 1(%[addrA]!);"
        "p.lbu %[b2], 1(%[addrB]!);"
        "p.lbu %[a3], 1(%[addrA]!);"
        "p.lbu %[b3], 1(%[addrB]!);"
        "p.lbu %[a4], 1(%[addrA]!);"
        "p.lbu %[b4], 1(%[addrB]!);"
        "p.mac %[c1], %[a1], %[b1];"
        "p.mac %[c2], %[a2], %[b2];"
        "p.mac %[c3], %[a3], %[b3];"
        "p.mac %[c4], %[a4], %[b4];"
        : [c1] "+r" (local_sum_1), [c2] "+r" (local_sum_2), [c3] "+r" (local_sum_3), [c4] "+r" (local_sum_4),
          [addrA] "+r" (in_a), [addrB] "+r" (in_b),
          [a1] "+r" (a1_tmp), [b1] "+r" (b1_tmp),
          [a2] "+r" (a2_tmp), [b2] "+r" (b2_tmp),
          [a3] "+r" (a3_tmp), [b3] "+r" (b3_tmp),
          [a4] "+r" (a4_tmp), [b4] "+r" (b4_tmp));
    }*/

    //for(uint32_t i = 0; i < N_vect; i++)
    do {
      local_sum_1 += ((*in_a++)*(*in_b++));
      local_sum_2 += ((*in_a++)*(*in_b++));
      local_sum_3 += ((*in_a++)*(*in_b++));
      local_sum_4 += ((*in_a++)*(*in_b++));
    } while(in_a<end);
    while(in_a<end_reminder){
      local_sum_1 += ((*in_a++)*(*in_b++));
    }

    // Reduction
    local_sum_1 += local_sum_2;
    local_sum_3 += local_sum_4;
    local_sum_1 += local_sum_3;
    *s = local_sum_1;
    mempool_stop_benchmark();

  }
  mempool_log_barrier(2,id); // wait until all cores have finished
}

/* Single-core dot-product unrolled4 */
void dotp_single_unrolled6 ( int32_t* in_a,
                            int32_t* in_b,
                            int32_t* s,
                            uint32_t N_vect,
                            uint32_t id) {
  if(id == 0) {

    int32_t local_sum_1 = 0;
    int32_t local_sum_2 = 0;
    int32_t local_sum_3 = 0;
    int32_t local_sum_4 = 0;
    int32_t local_sum_5 = 0;
    int32_t local_sum_6 = 0;
    //int32_t local_sum_7 = 0;
    //int32_t local_sum_8 = 0;
    int32_t* end = in_a + ((N_vect/6)*6);
    int32_t* end_reminder = in_a + N_vect;

    //for(uint32_t i = 0; i < N_vect; i++)
    do {
      local_sum_1 += ((*in_a++)*(*in_b++));
      local_sum_2 += ((*in_a++)*(*in_b++));
      local_sum_3 += ((*in_a++)*(*in_b++));
      local_sum_4 += ((*in_a++)*(*in_b++));
      local_sum_5 += ((*in_a++)*(*in_b++));
      local_sum_6 += ((*in_a++)*(*in_b++));
      //local_sum_7 += ((*in_a++)*(*in_b++));
      //local_sum_8 += ((*in_a++)*(*in_b++));
    } while(in_a<end);

    do {
      local_sum_1 += ((*in_a++)*(*in_b++));
    } while(in_a<end_reminder);

    // Reduction
    local_sum_1 += local_sum_2;
    local_sum_3 += local_sum_4;
    local_sum_5 += local_sum_6;
    local_sum_1 += local_sum_3;
    local_sum_1 += local_sum_5;

    *s = local_sum_1;
  }
  mempool_barrier(NUM_CORES); // wait until all cores have finished
}
