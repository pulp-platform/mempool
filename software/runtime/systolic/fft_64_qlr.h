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
// 64-point radix-4 DIT FFT using IQLRs for popping data from the queue and xqueue extension for pushing to the queue


#include "alloc.h"
#include "printf.h"
#include "synchronization.h"
#include "xpulp/builtins_v2.h"

// Dimensions of square systolic array
// TODO: SQRT ROOT OF NUM_CORES FOR SYSTOLIC SIZE
#define FFTLEN 64
#define NUM_STAGE 4
#define PE_PER_STAGE 16
#define ASM

// QLR configuration
#define QLR_CFG_T0 (QLR_CFG_BASE | (5 << 5))
#define QLR_CFG_T1 (QLR_CFG_BASE | (6 << 5))
#define QLR_CFG_T2 (QLR_CFG_BASE | (7 << 5))
#define QLR_CFG_T3 (QLR_CFG_BASE | (28 << 5))
#define QLR_CFG_TYPE 0
#define QLR_CFG_REQ 2
#define QLR_CFG_RF 3
#define QLR_CFG_IADDR 4
#define QLR_CFG_OADDR 5

// QLRs
register int32_t qlr_t0 asm("t0");
register int32_t qlr_t1 asm("t1");
register int32_t qlr_t2 asm("t2");
register int32_t qlr_t3 asm("t3");

// Array of queue ptrs
int32_t *queues_input_0[NUM_STAGE-1][PE_PER_STAGE];
int32_t *queues_input_1[NUM_STAGE-1][PE_PER_STAGE];
int32_t *queues_input_2[NUM_STAGE-1][PE_PER_STAGE];
int32_t *queues_input_3[NUM_STAGE-1][PE_PER_STAGE];

int32_t *queues_output_0[NUM_STAGE-1][PE_PER_STAGE];
int32_t *queues_output_1[NUM_STAGE-1][PE_PER_STAGE];
int32_t *queues_output_2[NUM_STAGE-1][PE_PER_STAGE];
int32_t *queues_output_3[NUM_STAGE-1][PE_PER_STAGE];

// queue push
static inline void queue_push(void *const queue, int32_t data,
                              int32_t *const ret) {
  asm volatile("q.push.w %0, %1, (%2)" : "+r"(*ret) : "r"(data), "r"(queue));
}

// queue pop
inline void queue_pop(void *const queue, int32_t *const ret) {
  asm volatile("q.pop.w %0, 0(%1)" : "=r"(*ret) : "r"(queue));
}

void shuffling_order_calc(int32_t *const shuffling_order){
  uint32_t sum,temp,digit,i;
  for (i=0;i<64;i++){
    sum = 0;
    temp = i;
    for (int j=0;j<3;j++){
      digit = temp%4;
      sum = sum*4 + digit;
      temp = temp/4;
    }
    shuffling_order[i] = sum;
  }

  uint32_t core_id,queue_id,core_id_o,queue_id_o;
  for (i=0;i<64;i++){
    core_id = i/4;
    queue_id = i%4;
    core_id_o = (core_id/4)*4 + queue_id;
    queue_id_o = core_id%4;
    shuffling_order[i + 64] = core_id_o*4 + queue_id_o;
  }

  for (i=0;i<64;i++){
    core_id = i/4;
    queue_id = i%4;
    core_id_o = core_id%4 + queue_id*4;
    queue_id_o = core_id/4;
    shuffling_order[i + 2*64] = core_id_o*4 + queue_id_o;
  }

  //Queue addressing and array addressing are reverse of each other
  for (i=0;i<64;i++){
    core_id = i/4;
    queue_id = i%4;
    core_id_o = core_id / 4 + queue_id*4;
    queue_id_o = core_id%4;
    shuffling_order[i + 3*64] = core_id_o*4 + queue_id_o;
  }

}

void systolic_init(uint32_t const *tile_mapping, uint32_t const *core_mapping, int32_t *const shuffling_order) {
  // Create systolic array via queues
  extern uint32_t __seq_start;
  uint32_t grid_pos = PE_PER_STAGE;
  uint32_t tile_id;
  uint32_t core_id;
  uint32_t tile_offset;
  uint32_t core_offset;
  for (uint32_t y = 1; y < NUM_STAGE; ++y) {
    for (uint32_t x = 0; x < PE_PER_STAGE; ++x) {
      core_id = core_mapping[grid_pos];
      core_offset = core_id * sizeof(int32_t);
      queues_input_0[y-1][x] = (int32_t *)(core_offset + 0);
      queues_input_1[y-1][x] = (int32_t *)(core_offset + 1);
      queues_input_2[y-1][x] = (int32_t *)(core_offset + 2);
      queues_input_3[y-1][x] = (int32_t *)(core_offset + 3);
      ++grid_pos;
    }
  }

  uint32_t tile_id_o[4], core_id_o[4], queue_id_o[4], tile_offset_o[4], core_offset_o[4], idx_out;
  for (uint32_t y = 0; y < (NUM_STAGE-1); ++y) {
    for (uint32_t x = 0; x < PE_PER_STAGE; ++x) {
      for (uint32_t i = 0; i < 4; ++i){
        idx_out       = shuffling_order[y*64 + x*4 + i];
        tile_id_o[i]  = tile_mapping[(y+1)*PE_PER_STAGE + idx_out/4];
        core_id_o[i]  = core_mapping[(y+1)*PE_PER_STAGE + idx_out/4];
        queue_id_o[i] = idx_out%4;

        tile_offset_o[i] = tile_id_o[i] * SEQ_MEM_SIZE;
        core_offset_o[i] = (core_id_o[i] % 4) * 4;
      }

      queues_output_0[y][x] = &__seq_start + tile_offset_o[0] + core_offset_o[0] + queue_id_o[0];
      queues_output_1[y][x] = &__seq_start + tile_offset_o[1] + core_offset_o[1] + queue_id_o[1];
      queues_output_2[y][x] = &__seq_start + tile_offset_o[2] + core_offset_o[2] + queue_id_o[2];
      queues_output_3[y][x] = &__seq_start + tile_offset_o[3] + core_offset_o[3] + queue_id_o[3];
    }
  }
}

//Front loading stage
void systolic_front_pe(uint32_t idx_in_stage){
  int32_t A, B, C, D;
  int32_t *queue_next_0;
  int32_t *queue_next_1;
  int32_t *queue_next_2;
  int32_t *queue_next_3;
  int32_t resp_0 __attribute__((unused)) = 0;
  int32_t resp_1 __attribute__((unused)) = 0;
  int32_t resp_2 __attribute__((unused)) = 0;
  int32_t resp_3 __attribute__((unused)) = 0;
  //Load Data
  A = *(int32_t *)&vector_inp[(4*idx_in_stage) * 2U];
  B = *(int32_t *)&vector_inp[(4*idx_in_stage + 1) * 2U];
  C = *(int32_t *)&vector_inp[(4*idx_in_stage + 2) * 2U];
  D = *(int32_t *)&vector_inp[(4*idx_in_stage + 3) * 2U];
  // Assign queues
  queue_next_0 = queues_output_0[0][idx_in_stage];
  queue_next_1 = queues_output_1[0][idx_in_stage];
  queue_next_2 = queues_output_2[0][idx_in_stage];
  queue_next_3 = queues_output_3[0][idx_in_stage];
  //Push data to the queues
  queue_push(queue_next_0, A, &resp_0);
  queue_push(queue_next_1, B, &resp_1);
  queue_push(queue_next_2, C, &resp_2);
  queue_push(queue_next_3, D, &resp_3);
}

//first fft stage
void systolic_first_fft_pe(uint32_t stage_idx, uint32_t idx_in_stage){
  int32_t O0, O1, O2, O3;
  int32_t *queue_next_0;
  int32_t *queue_next_1;
  int32_t *queue_next_2;
  int32_t *queue_next_3;

  volatile int32_t *qlr_cfg_t0 = (int32_t *)QLR_CFG_T0;
  volatile int32_t *qlr_cfg_t1 = (int32_t *)QLR_CFG_T1;
  volatile int32_t *qlr_cfg_t2 = (int32_t *)QLR_CFG_T2;
  volatile int32_t *qlr_cfg_t3 = (int32_t *)QLR_CFG_T3;

  // Assign queues
  queue_next_0 = queues_output_0[stage_idx][idx_in_stage];
  queue_next_1 = queues_output_1[stage_idx][idx_in_stage];
  queue_next_2 = queues_output_2[stage_idx][idx_in_stage];
  queue_next_3 = queues_output_3[stage_idx][idx_in_stage];

  int32_t reqs = 1;
  //Configure QLRs
  qlr_cfg_t0[QLR_CFG_REQ] = (int32_t)reqs;
  qlr_cfg_t0[QLR_CFG_IADDR] = (int32_t)queues_input_0[stage_idx-1][idx_in_stage];
  qlr_cfg_t1[QLR_CFG_REQ] = (int32_t)reqs;
  qlr_cfg_t1[QLR_CFG_IADDR] = (int32_t)queues_input_1[stage_idx-1][idx_in_stage];
  qlr_cfg_t2[QLR_CFG_REQ] = (int32_t)reqs;
  qlr_cfg_t2[QLR_CFG_IADDR] = (int32_t)queues_input_2[stage_idx-1][idx_in_stage];
  qlr_cfg_t3[QLR_CFG_REQ] = (int32_t)reqs;
  qlr_cfg_t3[QLR_CFG_IADDR] = (int32_t)queues_input_3[stage_idx-1][idx_in_stage];

  //Start QLR
  qlr_cfg_t0[QLR_CFG_TYPE] = 1;
  qlr_cfg_t1[QLR_CFG_TYPE] = 1;
  qlr_cfg_t2[QLR_CFG_TYPE] = 1;
  qlr_cfg_t3[QLR_CFG_TYPE] = 1;

  //Pop the inputs from the input queues
  asm volatile("":"=r"(qlr_t0),"=r"(qlr_t1),"=r"(qlr_t2),"=r"(qlr_t3));


  int16_t t0, t1, t2;
  v2s A, B, C, D, E, F, G, H;

  //Radix4 calculation
#ifndef ASM
  v2s s2 = {2, 2};
  B = (v2s) _SRA2((v2s)qlr_t1,s2);
  D = (v2s) _SRA2((v2s)qlr_t3,s2);
  A = (v2s) _SRA2((v2s)qlr_t0,s2);
  C = (v2s) _SRA2((v2s)qlr_t2,s2);

  E = (v2s) _ADD2(A,C);
  F = (v2s) _SUB2(A,C);
  G = (v2s) _ADD2(B,D);
  H = (v2s) _SUB2(B,D);

  t0 = (int16_t)H[0];
  t1 = (int16_t)H[1];

  A = (v2s) _PACK2(t0,-t1);

  O0 = (int32_t) _ADD2(E,G);
  O1 = (int32_t) _SUB2(F,A);
  O2 = (int32_t) _SUB2(E,G);
  O3 = (int32_t) _ADD2(A,F);
#else
  v2s s2;
  B = (v2s)qlr_t1;
  D = (v2s)qlr_t3;
  A = (v2s)qlr_t0;
  C = (v2s)qlr_t2;

  asm volatile("addi %[s2], zero, 0x02;"
               "slli %[s2], %[s2], 0x10;"
               "addi %[s2], %[s2], 0x02;"
               "pv.sra.h  %[B],%[B],%[s2];"
               "pv.sra.h  %[D],%[D],%[s2];"
               "pv.sra.h  %[A],%[A],%[s2];"
               "pv.sra.h  %[C],%[C],%[s2];"
               "pv.add.h  %[E],%[A],%[C];"
               "pv.sub.h  %[F],%[A],%[C];"
               "pv.add.h  %[G],%[B],%[D];"
               "pv.sub.h  %[H],%[B],%[D];"
               "pv.extract.h  %[t0],%[H],0;"
               "pv.extract.h  %[t1],%[H],1;"
               "sub %[t2],zero,%[t1];"
               "pv.pack %[A],%[t0],%[t2];"
               "pv.add.h  %[B],%[E],%[G];"
               "pv.sub.h  %[C],%[F],%[A];"
               "pv.sub.h  %[D],%[E],%[G];"
               "pv.add.h  %[H],%[A],%[F];"
               : [A] "+&r"(A), [B] "+&r"(B), [C] "+&r"(C), [D] "+&r"(D), [E] "=&r"(E),
               [F] "=&r"(F), [G] "=&r"(G), [H] "=&r"(H), [t0] "=&r"(t0),
               [t1] "=&r"(t1), [t2] "=&r"(t2), [s2] "=&r"(s2)
               :
               :);

  O0 = (int32_t)B;
  O1 = (int32_t)C;
  O2 = (int32_t)D;
  O3 = (int32_t)H;
#endif

  //Push the results to the output queue
  int32_t resp_0 __attribute__((unused)) = 0;
  int32_t resp_1 __attribute__((unused)) = 0;
  int32_t resp_2 __attribute__((unused)) = 0;
  int32_t resp_3 __attribute__((unused)) = 0;
  queue_push(queue_next_0, O0, &resp_0);
  queue_push(queue_next_1, O1, &resp_1);
  queue_push(queue_next_2, O2, &resp_2);
  queue_push(queue_next_3, O3, &resp_3);
}


//Middle stages

void systolic_mid_pe(uint32_t stage_idx, uint32_t idx_in_stage){
  int32_t O0, O1, O2, O3;
  int32_t *queue_next_0;
  int32_t *queue_next_1;
  int32_t *queue_next_2;
  int32_t *queue_next_3;
  volatile int32_t *qlr_cfg_t0 = (int32_t *)QLR_CFG_T0;
  volatile int32_t *qlr_cfg_t1 = (int32_t *)QLR_CFG_T1;
  volatile int32_t *qlr_cfg_t2 = (int32_t *)QLR_CFG_T2;
  volatile int32_t *qlr_cfg_t3 = (int32_t *)QLR_CFG_T3;

  // Assign queues
  queue_next_0 = queues_output_0[stage_idx][idx_in_stage];
  queue_next_1 = queues_output_1[stage_idx][idx_in_stage];
  queue_next_2 = queues_output_2[stage_idx][idx_in_stage];
  queue_next_3 = queues_output_3[stage_idx][idx_in_stage];

  int32_t reqs = 1;
  //Configure QLRs
  qlr_cfg_t0[QLR_CFG_REQ] = (int32_t)reqs;
  qlr_cfg_t0[QLR_CFG_IADDR] = (int32_t)queues_input_0[stage_idx-1][idx_in_stage];
  qlr_cfg_t1[QLR_CFG_REQ] = (int32_t)reqs;
  qlr_cfg_t1[QLR_CFG_IADDR] = (int32_t)queues_input_1[stage_idx-1][idx_in_stage];
  qlr_cfg_t2[QLR_CFG_REQ] = (int32_t)reqs;
  qlr_cfg_t2[QLR_CFG_IADDR] = (int32_t)queues_input_2[stage_idx-1][idx_in_stage];
  qlr_cfg_t3[QLR_CFG_REQ] = (int32_t)reqs;
  qlr_cfg_t3[QLR_CFG_IADDR] = (int32_t)queues_input_3[stage_idx-1][idx_in_stage];

  //Start QLR
  qlr_cfg_t0[QLR_CFG_TYPE] = 1;
  qlr_cfg_t1[QLR_CFG_TYPE] = 1;
  qlr_cfg_t2[QLR_CFG_TYPE] = 1;
  qlr_cfg_t3[QLR_CFG_TYPE] = 1;

  //Pop the inputs from the input queues
  asm volatile("":"=r"(qlr_t0),"=r"(qlr_t1),"=r"(qlr_t2),"=r"(qlr_t3));

  //twiddle coef calculation
  v2s CoSi1, CoSi2, CoSi3;
  v2s C1, C2, C3;
  int16_t t0, t1, t2, t3, t4, t5;
  int32_t ic;

  if (stage_idx == 2){
    ic = (idx_in_stage % 4) * 4;
    CoSi1 = *(v2s *)&twiddleCoef_q16[ic * 2U];
    CoSi2 = *(v2s *)&twiddleCoef_q16[2 * (ic * 2U)];
    CoSi3 = *(v2s *)&twiddleCoef_q16[3 * (ic * 2U)];
  }

#ifndef ASM
  t1 = (int16_t)CoSi1[0];
  t3 = (int16_t)CoSi2[0];
  t5 = (int16_t)CoSi3[0];
  t0 = (int16_t)CoSi1[1];
  t2 = (int16_t)CoSi2[1];
  t4 = (int16_t)CoSi3[1];
  C1 = __PACK2(-t0, t1);
  C2 = __PACK2(-t2, t3);
  C3 = __PACK2(-t4, t5);
#else
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
#endif

  v2s A, B, C, D, E, F, G, H;

// Radix4 calculation
#ifndef ASM
  v2s s1 = {1, 1};
  B = (v2s)qlr_t1;
  D = (v2s)qlr_t3;
  A = (v2s)qlr_t0;
  C = (v2s)qlr_t2;

  t0 = (int16_t) (_DOTP2(CoSi1,B) >> 16U);
  t1 = (int16_t) (_DOTP2(_PACK2(-CoSi1[1],CoSi1[0]),B) >> 16U);
  t2 = (int16_t) (_DOTP2(CoSi2,C) >> 16U);
  t3 = (int16_t) (_DOTP2(_PACK2(-CoSi2[1],CoSi2[0]),C) >> 16U);
  t4 = (int16_t) (_DOTP2(CoSi3,D) >> 16U);
  t5 = (int16_t) (_DOTP2(_PACK2(-CoSi3[1],CoSi3[0]),D) >> 16U);

  A = (v2s) _SRA2(A,s1);
  B = (v2s) _PACK2(t0,t1);
  C = (v2s) _PACK2(t2,t3);
  D = (v2s) _PACK2(t4,t5);

  E = (v2s) _ADD2(A,C);
  F = (v2s) _SUB2(A,C);
  G = (v2s) _ADD2(B,D);
  H = (v2s) _SUB2(B,D);
  E = (v2s) _SRA2(E,s1);
  F = (v2s) _SRA2(F,s1);
  G = (v2s) _SRA2(G,s1);
  H = (v2s) _SRA2(H,s1);

  t0 = (int16_t)H[0];
  t1 = (int16_t)H[1];

  A = (v2s) _PACK2(t0,-t1);

  O0 = (int32_t) _ADD2(E,G);
  O1 = (int32_t) _SUB2(F,A);
  O2 = (int32_t) _SUB2(E,G);
  O3 = (int32_t) _ADD2(A,F);
#else
  v2s s1;
  B = (v2s)qlr_t1;
  D = (v2s)qlr_t3;
  A = (v2s)qlr_t0;
  C = (v2s)qlr_t2;

  asm volatile("addi %[s1], zero, 0x01;"
               "slli %[s1], %[s1], 0x10;"
               "addi %[s1], %[s1], 0x01;"
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
               "pv.sra.h  %[A],%[A],%[s1];"
               "pv.pack %[B],%[t1],%[t0];"
               "pv.pack %[C],%[t3],%[t2];"
               "pv.pack %[D],%[t5],%[t4];"
               "pv.add.h  %[E],%[A],%[C];"
               "pv.sub.h  %[F],%[A],%[C];"
               "pv.add.h  %[G],%[B],%[D];"
               "pv.sub.h  %[H],%[B],%[D];"
               "pv.sra.h  %[E],%[E],%[s1];"
               "pv.sra.h  %[F],%[F],%[s1];"
               "pv.sra.h  %[G],%[G],%[s1];"
               "pv.sra.h  %[H],%[H],%[s1];"
               "pv.extract.h  %[t0],%[H],0;"
               "pv.extract.h  %[t1],%[H],1;"
               "sub %[t2],zero,%[t1];"
               "pv.pack %[A],%[t0],%[t2];"
               "pv.add.h  %[B],%[E],%[G];"
               "pv.sub.h  %[C],%[F],%[A];"
               "pv.sub.h  %[D],%[E],%[G];"
               "pv.add.h  %[H],%[A],%[F];"
               : [A] "+&r"(A), [B] "+&r"(B), [C] "+&r"(C), [D] "+&r"(D),
                 [E] "=&r"(E), [F] "=&r"(F), [G] "=&r"(G), [H] "=&r"(H),
                 [t0] "=&r"(t0), [t1] "=&r"(t1), [t2] "=&r"(t2), [t3] "=&r"(t3),
                 [t4] "=&r"(t4), [t5] "=&r"(t5), [s1] "=&r"(s1)
               : [C1] "r"(C1), [C2] "r"(C2), [C3] "r"(C3), [CoSi1] "r"(CoSi1),
                 [CoSi2] "r"(CoSi2), [CoSi3] "r"(CoSi3)
               :);

  O0 = (int32_t)B;
  O1 = (int32_t)C;
  O2 = (int32_t)D;
  O3 = (int32_t)H;
#endif

  //Push the results to the output queue
  int32_t resp_0 __attribute__((unused)) = 0;
  int32_t resp_1 __attribute__((unused)) = 0;
  int32_t resp_2 __attribute__((unused)) = 0;
  int32_t resp_3 __attribute__((unused)) = 0;
  queue_push(queue_next_0, O0, &resp_0);
  queue_push(queue_next_1, O1, &resp_1);
  queue_push(queue_next_2, O2, &resp_2);
  queue_push(queue_next_3, O3, &resp_3);
}

//Last stage
void systolic_end_pe(uint32_t idx_in_stage, int16_t *const vector_output, int32_t *const shuffling_order){
  int32_t O0, O1, O2, O3;
  volatile int32_t *qlr_cfg_t0 = (int32_t *)QLR_CFG_T0;
  volatile int32_t *qlr_cfg_t1 = (int32_t *)QLR_CFG_T1;
  volatile int32_t *qlr_cfg_t2 = (int32_t *)QLR_CFG_T2;
  volatile int32_t *qlr_cfg_t3 = (int32_t *)QLR_CFG_T3;

  int32_t reqs = 1;
  //Configure QLRs
  qlr_cfg_t0[QLR_CFG_REQ] = (int32_t)reqs;
  qlr_cfg_t0[QLR_CFG_IADDR] = (int32_t)queues_input_0[2][idx_in_stage];
  qlr_cfg_t1[QLR_CFG_REQ] = (int32_t)reqs;
  qlr_cfg_t1[QLR_CFG_IADDR] = (int32_t)queues_input_1[2][idx_in_stage];
  qlr_cfg_t2[QLR_CFG_REQ] = (int32_t)reqs;
  qlr_cfg_t2[QLR_CFG_IADDR] = (int32_t)queues_input_2[2][idx_in_stage];
  qlr_cfg_t3[QLR_CFG_REQ] = (int32_t)reqs;
  qlr_cfg_t3[QLR_CFG_IADDR] = (int32_t)queues_input_3[2][idx_in_stage];
  //write_csr(0, queues_input_0[2][idx_in_stage]);
  //Start QLR
  qlr_cfg_t0[QLR_CFG_TYPE] = 1;
  qlr_cfg_t1[QLR_CFG_TYPE] = 1;
  qlr_cfg_t2[QLR_CFG_TYPE] = 1;
  qlr_cfg_t3[QLR_CFG_TYPE] = 1;

  //Pop the inputs from the input queues
  asm volatile("":"=r"(qlr_t0),"=r"(qlr_t1),"=r"(qlr_t2),"=r"(qlr_t3));

  //twiddle coef calculation
  v2s CoSi1, CoSi2, CoSi3;
  v2s C1, C2, C3;
  int16_t t0, t1, t2, t3, t4, t5;
  int32_t ic;

  ic = idx_in_stage;
  CoSi1 = *(v2s *)&twiddleCoef_q16[ic * 2U];
  CoSi2 = *(v2s *)&twiddleCoef_q16[2 * (ic * 2U)];
  CoSi3 = *(v2s *)&twiddleCoef_q16[3 * (ic * 2U)];

#ifndef ASM
  t1 = (int16_t)CoSi1[0];
  t3 = (int16_t)CoSi2[0];
  t5 = (int16_t)CoSi3[0];
  t0 = (int16_t)CoSi1[1];
  t2 = (int16_t)CoSi2[1];
  t4 = (int16_t)CoSi3[1];
  C1 = __PACK2(-t0, t1);
  C2 = __PACK2(-t2, t3);
  C3 = __PACK2(-t4, t5);
#else
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
#endif

  v2s A, B, C, D, E, F, G, H;
//Radix4 calculation
#ifndef ASM
  v2s s1 = {1, 1};
  B = (v2s)qlr_t1;
  D = (v2s)qlr_t3;
  A = (v2s)qlr_t0;
  C = (v2s)qlr_t2;

  t0 = (int16_t) (_DOTP2(CoSi1,B) >> 16U);
  t1 = (int16_t) (_DOTP2(_PACK2(-CoSi1[1],CoSi1[0]),B) >> 16U);
  t2 = (int16_t) (_DOTP2(CoSi2,C) >> 16U);
  t3 = (int16_t) (_DOTP2(_PACK2(-CoSi2[1],CoSi2[0]),C) >> 16U);
  t4 = (int16_t) (_DOTP2(CoSi3,D) >> 16U);
  t5 = (int16_t) (_DOTP2(_PACK2(-CoSi3[1],CoSi3[0]),D) >> 16U);

  A = (v2s) _SRA2(A,s1);
  B = (v2s) _PACK2(t0,t1);
  C = (v2s) _PACK2(t2,t3);
  D = (v2s) _PACK2(t4,t5);

  E = (v2s) _ADD2(A,C);
  F = (v2s) _SUB2(A,C);
  G = (v2s) _ADD2(B,D);
  H = (v2s) _SUB2(B,D);
  E = (v2s) _SRA2(E,s1);
  F = (v2s) _SRA2(F,s1);
  G = (v2s) _SRA2(G,s1);
  H = (v2s) _SRA2(H,s1);

  t0 = (int16_t)H[0];
  t1 = (int16_t)H[1];

  A = (v2s) _PACK2(t0,-t1);

  O0 = (int32_t) _ADD2(E,G);
  O1 = (int32_t) _SUB2(F,A);
  O2 = (int32_t) _SUB2(E,G);
  O3 = (int32_t) _ADD2(A,F);
#else
  v2s s1;
  B = (v2s)qlr_t1;
  D = (v2s)qlr_t3;
  A = (v2s)qlr_t0;
  C = (v2s)qlr_t2;

  asm volatile("addi %[s1], zero, 0x01;"
               "slli %[s1], %[s1], 0x10;"
               "addi %[s1], %[s1], 0x01;"
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
               "pv.sra.h  %[A],%[A],%[s1];"
               "pv.pack %[B],%[t1],%[t0];"
               "pv.pack %[C],%[t3],%[t2];"
               "pv.pack %[D],%[t5],%[t4];"
               "pv.add.h  %[E],%[A],%[C];"
               "pv.sub.h  %[F],%[A],%[C];"
               "pv.add.h  %[G],%[B],%[D];"
               "pv.sub.h  %[H],%[B],%[D];"
               "pv.sra.h  %[E],%[E],%[s1];"
               "pv.sra.h  %[F],%[F],%[s1];"
               "pv.sra.h  %[G],%[G],%[s1];"
               "pv.sra.h  %[H],%[H],%[s1];"
               "pv.extract.h  %[t0],%[H],0;"
               "pv.extract.h  %[t1],%[H],1;"
               "sub %[t2],zero,%[t1];"
               "pv.pack %[A],%[t0],%[t2];"
               "pv.add.h  %[B],%[E],%[G];"
               "pv.sub.h  %[C],%[F],%[A];"
               "pv.sub.h  %[D],%[E],%[G];"
               "pv.add.h  %[H],%[A],%[F];"
               : [A] "+&r"(A), [B] "+&r"(B), [C] "+&r"(C), [D] "+&r"(D),
                 [E] "=&r"(E), [F] "=&r"(F), [G] "=&r"(G), [H] "=&r"(H),
                 [t0] "=&r"(t0), [t1] "=&r"(t1), [t2] "=&r"(t2), [t3] "=&r"(t3),
                 [t4] "=&r"(t4), [t5] "=&r"(t5), [s1] "=&r"(s1)
               : [C1] "r"(C1), [C2] "r"(C2), [C3] "r"(C3), [CoSi1] "r"(CoSi1),
                 [CoSi2] "r"(CoSi2), [CoSi3] "r"(CoSi3)
               :);

  O0 = (int32_t)B;
  O1 = (int32_t)C;
  O2 = (int32_t)D;
  O3 = (int32_t)H;
#endif

  //Store the results to the output vector
  uint32_t i0,i1,i2,i3;
  i0 = shuffling_order[3*64 + 4*idx_in_stage];
  i1 = shuffling_order[3*64 + 4*idx_in_stage + 1];
  i2 = shuffling_order[3*64 + 4*idx_in_stage + 2];
  i3 = shuffling_order[3*64 + 4*idx_in_stage + 3];
  *(int32_t *)&vector_output[i0 * 2U] = O0;
  *(int32_t *)&vector_output[i1 * 2U] = O1;
  *(int32_t *)&vector_output[i2 * 2U] = O2;
  *(int32_t *)&vector_output[i3 * 2U] = O3;
}
