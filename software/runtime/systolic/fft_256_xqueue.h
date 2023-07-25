// Copyright 2021 ETH Zurich and University of Bologna.
//
// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//    http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
// Author: Vaibhav Krishna, ETH Zurich
// Intial Implementation 256-point radix-4 DIT FFT. First stage uses xqueue extension for pushing even though QLRs are available.
// The output address calculation is revamped and instead of observation, a formulaic way is used to calculate address.
// For an optimized version look at fft_oqlr.h


#include "alloc.h"
#include "printf.h"
#include "synchronization.h"
#include "xpulp/builtins_v2.h"

#include "xqueue.h"
#include "qlr.h"

/* Convolution configuration */
#define RADIX        4                          // hardcoded, do not change
#define LEN_FFT      256                        // hardcoded, do not change
#define NUM_STAGES   (NUM_CORES_PER_TILE)       // hardcoded, do not change
#define PE_PER_STAGE ((LEN_FFT) / (NUM_STAGES)) // hardcoded, do not change
#define NUM_ITER     10

#if NUM_CORES_PER_TILE != 4
#error "Only supports 4 cores per tile (as RADIX, and NUM_STAGES)"
#endif

#define ASM

// Array of queue ptrs
uint32_t *queues_out_0[NUM_STAGES-1][PE_PER_STAGE];
uint32_t *queues_out_1[NUM_STAGES-1][PE_PER_STAGE];
uint32_t *queues_out_2[NUM_STAGES-1][PE_PER_STAGE];
uint32_t *queues_out_3[NUM_STAGES-1][PE_PER_STAGE];

// Global arrays
uint16_t core_mapping[NUM_STAGES][PE_PER_STAGE] __attribute__((section(".l1")));
uint16_t shuffling_order[NUM_STAGES][LEN_FFT] __attribute__((section(".l1")));
int16_t pSrc[2048] __attribute__((aligned(2048), section(".l1")));
int16_t  vector_output[2*LEN_FFT] __attribute__((section(".l1")));

void input_shuffling_order_r4(uint32_t stage_i, uint16_t* order){
  // stage index in the inverted order (= remaining stages)
  uint32_t stage_i_inv = NUM_STAGES - (stage_i + 1);
  // number of point groups in this stage
  // '2 *' because at every stage, num_groups reduces by a factor of RADIX (= 4)
  // 2 because it is SQRT(RADIX)
  uint32_t num_groups = (uint32_t)1 << (2 * stage_i_inv); // 2^(2*(NUM_STAGES - (stage_i + 1)))
  // number of points in each group
  uint16_t num_points_group = (uint16_t)(LEN_FFT / num_groups);

  // for every group (of num_points_group elements) in this stage
  for (uint32_t i = 0; i < num_groups; i++){
    // for each subgroup of RADIX points each
    // i.e., take the first one and then offset the following ones
    for (uint32_t j = 0; j < num_points_group; j += RADIX){
      order[i*num_points_group + j + 0] = (uint16_t)((uint16_t)i*num_points_group + (uint16_t)j / RADIX);
      order[i*num_points_group + j + 1] = (uint16_t)(order[(uint16_t)i*num_points_group + (uint16_t)j + 0] + num_points_group / RADIX);
      order[i*num_points_group + j + 2] = (uint16_t)(order[(uint16_t)i*num_points_group + (uint16_t)j + 1] + num_points_group / RADIX);
      order[i*num_points_group + j + 3] = (uint16_t)(order[(uint16_t)i*num_points_group + (uint16_t)j + 2] + num_points_group / RADIX);
    }
  }
}

void invert_shuffling_order(uint16_t* order, uint16_t* reverse_order){
  uint16_t temp;
  for (uint32_t i = 0; i < LEN_FFT; i++){
    temp = order[i];
    reverse_order[temp] = (uint16_t)i;
  }
}

void shuffling_order_calc(){
  /* Stage structure */
  // stage 0 includes inputs (not shuffled)
  // the FFT computing stages are 4 (0,1,2,3)
  // stage 4 only contains the output of stage 3 with the last shuffling layer

  uint16_t *temp_next;
  uint16_t *temp_inv;
  temp_next = (uint16_t *)simple_malloc(LEN_FFT * sizeof(uint16_t));
  temp_inv  = (uint16_t *)simple_malloc(LEN_FFT * sizeof(uint16_t));

  input_shuffling_order_r4(1, temp_next);
  for (uint32_t i = 0; i < LEN_FFT; i++){
    shuffling_order[0][i] = temp_next[i];
  }

  for (uint32_t stage_i = 1; stage_i < (NUM_STAGES - 1); stage_i++){
    invert_shuffling_order(temp_next, temp_inv);
    input_shuffling_order_r4(stage_i + 1, temp_next);
    for (uint32_t i = 0; i < LEN_FFT; i++){
      shuffling_order[stage_i][i] = temp_inv[temp_next[i]];
    }
  }

  for (uint32_t i = 0; i < LEN_FFT; i++){
    shuffling_order[NUM_STAGES - 1][i] = temp_next[i];
  }

  simple_free(temp_inv);
  simple_free(temp_next);
}

void systolic_init(uint32_t stage_i, uint32_t pe_i) {
  // Create systolic array via queues
  extern uint8_t __seq_start;
  uint32_t index_out;
  //TODO: Fix all the "4"
  uint32_t tile_id_out[NUM_QUEUES_PER_CORE], core_id_out[NUM_QUEUES_PER_CORE], queue_id_out[NUM_QUEUES_PER_CORE];
  uint32_t tile_offset[NUM_QUEUES_PER_CORE], core_offset[NUM_QUEUES_PER_CORE], queue_offset[NUM_QUEUES_PER_CORE];

  // Compute output PEs for all stages, but the last one
  if (stage_i < (NUM_STAGES - 1)) {
    // Each PE has 4 outputs: make them correspond to the 4 available queues of each PE
    for (uint32_t i = 0; i < NUM_QUEUES_PER_CORE; i++){
      index_out = shuffling_order[stage_i][(pe_i * RADIX) + i];
      core_id_out[i]  = core_mapping[stage_i + 1][index_out / RADIX];
      tile_id_out[i]  = core_id_out[i] / NUM_CORES_PER_TILE;
      queue_id_out[i] = index_out % RADIX;

      // base address of this tile's sequential memory region
      tile_offset[i] = tile_id_out[i] * NUM_CORES_PER_TILE * SEQ_MEM_SIZE;
      // next address goes to next bank, then wrap around tile sequential region
      core_offset[i] = (core_id_out[i] % NUM_CORES_PER_TILE) * NUM_QUEUES_PER_CORE * sizeof(int32_t);
      // each PE has 4 outputs, same number as queues: decide which out queue must be fed with output i
      queue_offset[i] = queue_id_out[i] * sizeof(int32_t);
    }

    queues_out_0[stage_i][pe_i] = (uint32_t*)((uint32_t)(&__seq_start) + tile_offset[0] + core_offset[0] + queue_offset[0]);
    queues_out_1[stage_i][pe_i] = (uint32_t*)((uint32_t)(&__seq_start) + tile_offset[1] + core_offset[1] + queue_offset[1]);
    queues_out_2[stage_i][pe_i] = (uint32_t*)((uint32_t)(&__seq_start) + tile_offset[2] + core_offset[2] + queue_offset[2]);
    queues_out_3[stage_i][pe_i] = (uint32_t*)((uint32_t)(&__seq_start) + tile_offset[3] + core_offset[3] + queue_offset[3]);
  }
}

//first fft stage
void systolic_first_fft_pe(uint32_t stage_idx, uint32_t idx_in_stage){
  int32_t O0, O1, O2, O3;
  uint32_t *queue_next_0;
  uint32_t *queue_next_1;
  uint32_t *queue_next_2;
  uint32_t *queue_next_3;

  // Assign queues
  queue_next_0 = queues_out_0[stage_idx][idx_in_stage];
  queue_next_1 = queues_out_1[stage_idx][idx_in_stage];
  queue_next_2 = queues_out_2[stage_idx][idx_in_stage];
  queue_next_3 = queues_out_3[stage_idx][idx_in_stage];

  int16_t t0, t1, t2;
  v2s A, B, C, D, E, F, G, H;
  //uint16_t i0,i1,i2,i3;
  int16_t sum,temp,digit,i, j,i0[4];
  for (i=0;i<4;i++){
    sum = 0;
    temp = idx_in_stage*4 +i;
    for (j=0;j<NUM_STAGES;j++){
      digit = temp%4;
      sum = sum*4 + digit;
      temp = temp/4;
    }
    i0[i] = sum;
  }

  //Radix4 calculation
  v2s s2;
  int32_t resp_0 __attribute__((unused)) = 0;
  int32_t resp_1 __attribute__((unused)) = 0;
  int32_t resp_2 __attribute__((unused)) = 0;
  int32_t resp_3 __attribute__((unused)) = 0;
  asm volatile("addi %[s2], zero, 0x02;"
              "slli %[s2], %[s2], 0x10;"
              "addi %[s2], %[s2], 0x02;"
              :[s2] "=&r"(s2)
              :);
  for (i=0;i<NUM_ITER;i++){
    j = i%4;
    A = *(v2s *)&pSrc[(i0[0] + j*LEN_FFT) * 2U];
    B = *(v2s *)&pSrc[(i0[1] + j*LEN_FFT) * 2U];
    C = *(v2s *)&pSrc[(i0[2] + j*LEN_FFT) * 2U];
    D = *(v2s *)&pSrc[(i0[3] + j*LEN_FFT) * 2U];

    asm volatile(//"addi %[s2], zero, 0x02;"
                //"slli %[s2], %[s2], 0x10;"
                //"addi %[s2], %[s2], 0x02;"
                "pv.sra.h  %[A],%[A],%[s2];"
                "pv.sra.h  %[C],%[C],%[s2];"
                "pv.sra.h  %[B],%[B],%[s2];"
                "pv.sra.h  %[D],%[D],%[s2];"
                "pv.add.h  %[E],%[A],%[C];"
                "pv.sub.h  %[F],%[A],%[C];"
                "pv.sub.h  %[H],%[B],%[D];"
                "pv.add.h  %[G],%[B],%[D];"
                "pv.extract.h  %[t0],%[H],0;"
                "pv.extract.h  %[t1],%[H],1;"
                "sub %[t2],zero,%[t1];"
                "pv.pack %[A],%[t0],%[t2];"
                "pv.add.h  %[B],%[E],%[G];"
                "pv.sub.h  %[D],%[E],%[G];"
                "pv.sub.h  %[C],%[F],%[A];"
                "pv.add.h  %[H],%[A],%[F];"
                : [A] "+&r"(A), [B] "+&r"(B), [C] "+&r"(C), [D] "+&r"(D), [E] "=&r"(E),
                [F] "=&r"(F), [G] "=&r"(G), [H] "=&r"(H), [t0] "=&r"(t0),
                [t1] "=&r"(t1), [t2] "=&r"(t2)
                :[s2] "r"(s2)
                :);

    O0 = (int32_t)B;
    O1 = (int32_t)C;
    O2 = (int32_t)D;
    O3 = (int32_t)H;

    //Push the results to the output queue
    queue_push(queue_next_0, O0, &resp_0);
    queue_push(queue_next_1, O1, &resp_1);
    queue_push(queue_next_2, O2, &resp_2);
    queue_push(queue_next_3, O3, &resp_3);
  }
}


//Middle stages

void systolic_mid_pe(uint32_t stage_idx, uint32_t idx_in_stage, uint32_t core_id){
  int32_t O0, O1, O2, O3;
  uint32_t *queue_next_0;
  uint32_t *queue_next_1;
  uint32_t *queue_next_2;
  uint32_t *queue_next_3;
  volatile int32_t *qlr_cfg_t0 = (int32_t *)QLR_CFG_T0;
  volatile int32_t *qlr_cfg_t1 = (int32_t *)QLR_CFG_T1;
  volatile int32_t *qlr_cfg_t2 = (int32_t *)QLR_CFG_T2;
  volatile int32_t *qlr_cfg_t3 = (int32_t *)QLR_CFG_T3;
  uint32_t core_offset = core_id * sizeof(int32_t);
  // Assign queues
  queue_next_0 = queues_out_0[stage_idx][idx_in_stage];
  queue_next_1 = queues_out_1[stage_idx][idx_in_stage];
  queue_next_2 = queues_out_2[stage_idx][idx_in_stage];
  queue_next_3 = queues_out_3[stage_idx][idx_in_stage];

  int32_t reqs = NUM_ITER;
  //Configure QLRs
  qlr_cfg_t0[QLR_CFG_REQ] = (int32_t)reqs;
  qlr_cfg_t0[QLR_CFG_IADDR] = (int32_t)(core_offset + 0);
  qlr_cfg_t1[QLR_CFG_REQ] = (int32_t)reqs;
  qlr_cfg_t1[QLR_CFG_IADDR] = (int32_t)(core_offset + 1);
  qlr_cfg_t2[QLR_CFG_REQ] = (int32_t)reqs;
  qlr_cfg_t2[QLR_CFG_IADDR] = (int32_t)(core_offset + 2);
  qlr_cfg_t3[QLR_CFG_REQ] = (int32_t)reqs;
  qlr_cfg_t3[QLR_CFG_IADDR] = (int32_t)(core_offset + 3);

  //Start QLR
  qlr_cfg_t0[QLR_CFG_TYPE] = 1;
  qlr_cfg_t1[QLR_CFG_TYPE] = 1;
  qlr_cfg_t2[QLR_CFG_TYPE] = 1;
  qlr_cfg_t3[QLR_CFG_TYPE] = 1;

  //twiddle coef calculation
  v2s CoSi1, CoSi2, CoSi3;
  v2s C1, C2, C3;
  int16_t t0, t1, t2, t3, t4, t5;
  int32_t ic, nvar_group_by_4, twiddle_multiplier;

  nvar_group_by_4 = 1 << (2*(stage_idx));//4^(stage_idx)
  twiddle_multiplier = 1 <<(2*(NUM_STAGES-stage_idx-1));//4^(NUM_STAGES-stage_idx-1)

  ic = (idx_in_stage % nvar_group_by_4) * twiddle_multiplier;

  CoSi1 = *(v2s *)&twiddleCoef_q16[ic * 2U];
  CoSi2 = *(v2s *)&twiddleCoef_q16[2 * (ic * 2U)];
  CoSi3 = *(v2s *)&twiddleCoef_q16[3 * (ic * 2U)];


  asm volatile("pv.extract.h  %[t1],%[CoSi1],0;"
                "pv.extract.h  %[t3],%[CoSi2],0;"
                "pv.extract.h  %[t5],%[CoSi3],0;"
                "pv.extract.h  %[t0],%[CoSi1],1;"
                "pv.extract.h  %[t2],%[CoSi2],1;"
                "pv.extract.h  %[t4],%[CoSi3],1;"
                "sub           %[t0],zero,%[t0];"
                "sub           %[t2],zero,%[t2];"
                "sub           %[t4],zero,%[t4];"
                "pv.pack %[C1],%[t1],%[t0];"
                "pv.pack %[C2],%[t3],%[t2];"
                "pv.pack %[C3],%[t5],%[t4];"
                : [C1] "=r"(C1), [C2] "=r"(C2), [C3] "=r"(C3), [t0] "=&r"(t0),
                  [t1] "=&r"(t1), [t2] "=&r"(t2), [t3] "=&r"(t3),
                  [t4] "=&r"(t4), [t5] "=&r"(t5)
                : [CoSi1] "r"(CoSi1), [CoSi2] "r"(CoSi2), [CoSi3] "r"(CoSi3)
                :);

  v2s A, B, C, D, E, F, G, H;

// Radix4 calculation
  v2s s1;
  int32_t resp_0 __attribute__((unused)) = 0;
  int32_t resp_1 __attribute__((unused)) = 0;
  int32_t resp_2 __attribute__((unused)) = 0;
  int32_t resp_3 __attribute__((unused)) = 0;
  asm volatile("addi %[s1], zero, 0x01;"
              "slli %[s1], %[s1], 0x10;"
              "addi %[s1], %[s1], 0x01;"
              :[s1] "=&r"(s1)
              :);
  for(int32_t i=0;i<reqs;i++){
    __asm__ __volatile__("" : "=r"(qlr_t0), "=r"(qlr_t1),"=r"(qlr_t2),"=r"(qlr_t3));
    B = (v2s)qlr_t1;
    D = (v2s)qlr_t3;
    A = (v2s)qlr_t0;
    C = (v2s)qlr_t2;

    asm volatile(//"addi %[s1], zero, 0x01;"
                //"slli %[s1], %[s1], 0x10;"
                //"addi %[s1], %[s1], 0x01;"
                "pv.dotsp.h  %[E],%[CoSi1],%[B];"
                "pv.dotsp.h  %[F],%[C1],%[B];"
                "pv.dotsp.h  %[G],%[CoSi2],%[C];"
                "pv.dotsp.h  %[H],%[C2],%[C];"
                "srai  %[t0],%[E],0x10;"
                "srai  %[t1],%[F],0x10;"
                "pv.dotsp.h  %[E],%[CoSi3],%[D];"
                "pv.dotsp.h  %[F],%[C3],%[D];"
                "srai  %[t2],%[G],0x10;"
                "srai  %[t3],%[H],0x10;"
                "srai  %[t4],%[E],0x10;"
                "srai  %[t5],%[F],0x10;"
                "pv.pack %[B],%[t1],%[t0];"
                "pv.pack %[D],%[t5],%[t4];"
                "pv.pack %[C],%[t3],%[t2];"
                "pv.sra.h  %[A],%[A],%[s1];"
                "pv.sub.h  %[H],%[B],%[D];"
                "pv.add.h  %[E],%[A],%[C];"
                "pv.sub.h  %[F],%[A],%[C];"
                "pv.sra.h  %[H],%[H],%[s1];"
                "pv.add.h  %[G],%[B],%[D];"
                "pv.sra.h  %[E],%[E],%[s1];"
                "pv.extract.h  %[t0],%[H],0;"
                "pv.extract.h  %[t1],%[H],1;"
                "pv.sra.h  %[F],%[F],%[s1];"
                "pv.sra.h  %[G],%[G],%[s1];"
                "sub %[t2],zero,%[t1];"
                "pv.pack %[A],%[t0],%[t2];"
                "pv.add.h  %[B],%[E],%[G];"
                "pv.sub.h  %[D],%[E],%[G];"
                "pv.sub.h  %[C],%[F],%[A];"
                "pv.add.h  %[H],%[A],%[F];"
                : [A] "+&r"(A), [B] "+&r"(B), [C] "+&r"(C), [D] "+&r"(D),
                  [E] "=&r"(E), [F] "=&r"(F), [G] "=&r"(G), [H] "=&r"(H),
                  [t0] "=&r"(t0), [t1] "=&r"(t1), [t2] "=&r"(t2), [t3] "=&r"(t3),
                  [t4] "=&r"(t4), [t5] "=&r"(t5)
                : [C1] "r"(C1), [C2] "r"(C2), [C3] "r"(C3), [CoSi1] "r"(CoSi1),
                  [CoSi2] "r"(CoSi2), [CoSi3] "r"(CoSi3), [s1] "r"(s1)
                :);

    O0 = (int32_t)B;
    O1 = (int32_t)C;
    O2 = (int32_t)D;
    O3 = (int32_t)H;

    //Push the results to the output queue
    queue_push(queue_next_0, O0, &resp_0);
    queue_push(queue_next_1, O1, &resp_1);
    queue_push(queue_next_2, O2, &resp_2);
    queue_push(queue_next_3, O3, &resp_3);
  }
}

//Last stage
void systolic_end_pe(uint32_t stage_idx, uint32_t idx_in_stage, uint32_t core_id){
  int32_t O0, O1, O2, O3;
  volatile int32_t *qlr_cfg_t0 = (int32_t *)QLR_CFG_T0;
  volatile int32_t *qlr_cfg_t1 = (int32_t *)QLR_CFG_T1;
  volatile int32_t *qlr_cfg_t2 = (int32_t *)QLR_CFG_T2;
  volatile int32_t *qlr_cfg_t3 = (int32_t *)QLR_CFG_T3;
  uint32_t core_offset = core_id * sizeof(int32_t);

  int32_t reqs = NUM_ITER;
  //Configure QLRs
  qlr_cfg_t0[QLR_CFG_REQ] = (int32_t)reqs;
  qlr_cfg_t0[QLR_CFG_IADDR] = (int32_t)(core_offset + 0);
  qlr_cfg_t1[QLR_CFG_REQ] = (int32_t)reqs;
  qlr_cfg_t1[QLR_CFG_IADDR] = (int32_t)(core_offset + 1);
  qlr_cfg_t2[QLR_CFG_REQ] = (int32_t)reqs;
  qlr_cfg_t2[QLR_CFG_IADDR] = (int32_t)(core_offset + 2);
  qlr_cfg_t3[QLR_CFG_REQ] = (int32_t)reqs;
  qlr_cfg_t3[QLR_CFG_IADDR] = (int32_t)(core_offset + 3);

  //Start QLR
  qlr_cfg_t0[QLR_CFG_TYPE] = 1;
  qlr_cfg_t1[QLR_CFG_TYPE] = 1;
  qlr_cfg_t2[QLR_CFG_TYPE] = 1;
  qlr_cfg_t3[QLR_CFG_TYPE] = 1;

  //twiddle coef calculation
  v2s CoSi1, CoSi2, CoSi3;
  v2s C1, C2, C3;
  int16_t t0, t1, t2, t3, t4, t5;
  int32_t ic;

  ic = idx_in_stage;
  CoSi1 = *(v2s *)&twiddleCoef_q16[ic * 2U];
  CoSi2 = *(v2s *)&twiddleCoef_q16[2 * (ic * 2U)];
  CoSi3 = *(v2s *)&twiddleCoef_q16[3 * (ic * 2U)];

  asm volatile("pv.extract.h  %[t1],%[CoSi1],0;"
                "pv.extract.h  %[t3],%[CoSi2],0;"
                "pv.extract.h  %[t5],%[CoSi3],0;"
                "pv.extract.h  %[t0],%[CoSi1],1;"
                "pv.extract.h  %[t2],%[CoSi2],1;"
                "pv.extract.h  %[t4],%[CoSi3],1;"
                "sub           %[t0],zero,%[t0];"
                "sub           %[t2],zero,%[t2];"
                "sub           %[t4],zero,%[t4];"
                "pv.pack %[C1],%[t1],%[t0];"
                "pv.pack %[C2],%[t3],%[t2];"
                "pv.pack %[C3],%[t5],%[t4];"
                : [C1] "=r"(C1), [C2] "=r"(C2), [C3] "=r"(C3), [t0] "=&r"(t0),
                  [t1] "=&r"(t1), [t2] "=&r"(t2), [t3] "=&r"(t3),
                  [t4] "=&r"(t4), [t5] "=&r"(t5)
                : [CoSi1] "r"(CoSi1), [CoSi2] "r"(CoSi2), [CoSi3] "r"(CoSi3)
                :);

  v2s A, B, C, D, E, F, G, H;
  uint32_t i0,i1,i2,i3;
  i0 = shuffling_order[3][4*idx_in_stage + 0];
  i1 = shuffling_order[3][4*idx_in_stage + 1];
  i2 = shuffling_order[3][4*idx_in_stage + 2];
  i3 = shuffling_order[3][4*idx_in_stage + 3];
//Radix4 calculation
  v2s s1;
  asm volatile("addi %[s1], zero, 0x01;"
              "slli %[s1], %[s1], 0x10;"
              "addi %[s1], %[s1], 0x01;"
              :[s1] "=&r"(s1)
              :);
  for(int32_t i=0;i<reqs;i++){
    __asm__ __volatile__("" : "=r"(qlr_t0), "=r"(qlr_t1),"=r"(qlr_t2),"=r"(qlr_t3));
    B = (v2s)qlr_t1;
    D = (v2s)qlr_t3;
    A = (v2s)qlr_t0;
    C = (v2s)qlr_t2;

    asm volatile(//"addi %[s1], zero, 0x01;"
                //"slli %[s1], %[s1], 0x10;"
                //"addi %[s1], %[s1], 0x01;"
                "pv.dotsp.h  %[E],%[CoSi1],%[B];"
                "pv.dotsp.h  %[F],%[C1],%[B];"
                "pv.dotsp.h  %[G],%[CoSi2],%[C];"
                "pv.dotsp.h  %[H],%[C2],%[C];"
                "srai  %[t0],%[E],0x10;"
                "srai  %[t1],%[F],0x10;"
                "pv.dotsp.h  %[E],%[CoSi3],%[D];"
                "pv.dotsp.h  %[F],%[C3],%[D];"
                "srai  %[t2],%[G],0x10;"
                "srai  %[t3],%[H],0x10;"
                "srai  %[t4],%[E],0x10;"
                "srai  %[t5],%[F],0x10;"
                "pv.pack %[B],%[t1],%[t0];"
                "pv.pack %[D],%[t5],%[t4];"
                "pv.pack %[C],%[t3],%[t2];"
                "pv.sra.h  %[A],%[A],%[s1];"
                "pv.sub.h  %[H],%[B],%[D];"
                "pv.add.h  %[E],%[A],%[C];"
                "pv.sub.h  %[F],%[A],%[C];"
                "pv.sra.h  %[H],%[H],%[s1];"
                "pv.add.h  %[G],%[B],%[D];"
                "pv.sra.h  %[E],%[E],%[s1];"
                "pv.extract.h  %[t0],%[H],0;"
                "pv.extract.h  %[t1],%[H],1;"
                "pv.sra.h  %[F],%[F],%[s1];"
                "pv.sra.h  %[G],%[G],%[s1];"
                "sub %[t2],zero,%[t1];"
                "pv.pack %[A],%[t0],%[t2];"
                "pv.add.h  %[B],%[E],%[G];"
                "pv.sub.h  %[D],%[E],%[G];"
                "pv.sub.h  %[C],%[F],%[A];"
                "pv.add.h  %[H],%[A],%[F];"
                : [A] "+&r"(A), [B] "+&r"(B), [C] "+&r"(C), [D] "+&r"(D),
                  [E] "=&r"(E), [F] "=&r"(F), [G] "=&r"(G), [H] "=&r"(H),
                  [t0] "=&r"(t0), [t1] "=&r"(t1), [t2] "=&r"(t2), [t3] "=&r"(t3),
                  [t4] "=&r"(t4), [t5] "=&r"(t5)
                : [C1] "r"(C1), [C2] "r"(C2), [C3] "r"(C3), [CoSi1] "r"(CoSi1),
                  [CoSi2] "r"(CoSi2), [CoSi3] "r"(CoSi3), [s1] "r"(s1)
                :);

    O0 = (int32_t)B;
    O1 = (int32_t)C;
    O2 = (int32_t)D;
    O3 = (int32_t)H;

    //Store the results to the output vector
    *(int32_t *)&vector_output[i0 * 2U] = O0;
    *(int32_t *)&vector_output[i1 * 2U] = O1;
    *(int32_t *)&vector_output[i2 * 2U] = O2;
    *(int32_t *)&vector_output[i3 * 2U] = O3;
  }
}
