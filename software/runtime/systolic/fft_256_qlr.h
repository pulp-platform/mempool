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
// 256-point radix-4 DIT FFT. Many optimizations were made when compared to fft_256.h:
// - Digit reversed order calculation moved to the first stage to reduce the initial address calculation time
// - OQLRs used in first stage to remove xqueue push instruction
// - First stage loop is unrolled and post-increment load instructions used too remove the address calculation overhead
// - Calculation of constant shift values s1 and s2 moved out of loop, to reduce instruction s in the loop.
// - Xqueue push instructions moved out of dedicated functions and directly used to reduce stack accesses.
// - Number of registers used in the kernel reduced to fit the twiddle factors and the output addresses inside the register file.


#include "alloc.h"
#include "printf.h"
#include "synchronization.h"
#include "xpulp/builtins_v2.h"


#define FFTLEN 256
#define NUM_STAGE 4
#define PE_PER_STAGE 64
#define ASM
#define NUM_ITER 100

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
int32_t *queues_output_0[NUM_STAGE-2][PE_PER_STAGE];
int32_t *queues_output_1[NUM_STAGE-2][PE_PER_STAGE];
int32_t *queues_output_2[NUM_STAGE-2][PE_PER_STAGE];
int32_t *queues_output_3[NUM_STAGE-2][PE_PER_STAGE];
//qlr queue ptr
int32_t queues_output_0_qlr[PE_PER_STAGE];
int32_t queues_output_1_qlr[PE_PER_STAGE];
int32_t queues_output_2_qlr[PE_PER_STAGE];
int32_t queues_output_3_qlr[PE_PER_STAGE];

//Global arrays
uint16_t tile_mapping[FFTLEN] __attribute__((section(".l1")));
uint16_t core_mapping[FFTLEN] __attribute__((section(".l1")));
uint16_t shuffling_order[FFTLEN * (NUM_STAGE)] __attribute__((section(".l1")));
int16_t pSrc[2048] __attribute__((aligned(2048), section(".l1")));
int16_t  vector_output[2*FFTLEN] __attribute__((section(".l1")));

// queue push
static inline void queue_push(void *const queue, int32_t data,
                              int32_t *const ret) {
  asm volatile("q.push.w %0, %1, (%2)" : "+r"(*ret) : "r"(data), "r"(queue));
}

// queue pop
inline void queue_pop(void *const queue, int32_t *const ret) {
  asm volatile("q.pop.w %0, 0(%1)" : "=r"(*ret) : "r"(queue));
}

void input_shuffling_order_r4(uint16_t nvar, uint16_t stage, int16_t* order){
  uint16_t n_group, nvar_group, i, j;
  n_group = 1 << (2*(NUM_STAGE-stage));
  nvar_group = nvar/n_group;
  for (i=0;i<n_group;i++){
    for (j=0;j<(nvar_group/4);j++){
      order[i*nvar_group + 4*j] = i*nvar_group + j;
      order[i*nvar_group + 4*j + 1] = order[i*nvar_group + 4*j] + nvar_group/4;
      order[i*nvar_group + 4*j + 2] = order[i*nvar_group + 4*j + 1] + nvar_group/4;
      order[i*nvar_group + 4*j + 3] = order[i*nvar_group + 4*j + 2] + nvar_group/4;
    }
  }
}

void invert_shuffling_order(int16_t* order, int16_t* reverse){
  int16_t temp;
  for (uint16_t i=0;i<FFTLEN;i++){
    temp = order[i];
    reverse[temp] = i;
  }
}

void shuffling_order_calc(){
  uint16_t *temp_next;
  uint16_t *temp_inv;
  temp_next    = (uint16_t *)simple_malloc(FFTLEN * sizeof(uint16_t));
  temp_inv     = (uint16_t *)simple_malloc(FFTLEN * sizeof(uint16_t));
  int16_t i,j;
  input_shuffling_order_r4(FFTLEN, 2, temp_next);

  for (i=0;i<FFTLEN;i++){
    shuffling_order[i] = temp_next[i];
  }

  invert_shuffling_order(temp_next, temp_inv);
  input_shuffling_order_r4(FFTLEN, 3, temp_next);

  for (i=0;i<FFTLEN;i++){
    j = temp_next[i];
    shuffling_order[i + FFTLEN] = temp_inv[j];
  }

  invert_shuffling_order(temp_next, temp_inv);
  input_shuffling_order_r4(FFTLEN, 4, temp_next);

  for (i=0;i<FFTLEN;i++){
    j = temp_next[i];
    shuffling_order[i + 2*FFTLEN] = temp_inv[j];
  }

  //Queue addressing and array addressing are reverse of each other
  for (i=0;i<FFTLEN;i++){
    shuffling_order[i + 3*FFTLEN] = temp_next[i];
  }
  simple_free(temp_inv);
  simple_free(temp_next);
}

void systolic_init() {
  // Create systolic array via queues
  extern uint32_t __seq_start;
  uint32_t tile_id_o[4], core_id_o[4], queue_id_o[4], tile_offset_o[4], core_offset_o[4], idx_out;
  //First stage uses OQLRs
  for (uint32_t x = 0; x < PE_PER_STAGE; ++x) {
    for (uint32_t i = 0; i < 4; ++i){
      idx_out       = shuffling_order[x*4 + i];
      core_id_o[i]  = core_mapping[PE_PER_STAGE + idx_out/4];
      queue_id_o[i] = idx_out%4;

      core_offset_o[i] = core_id_o[i] * sizeof(int32_t);
    }

    queues_output_0_qlr[x] = (core_offset_o[0] + queue_id_o[0]);
    queues_output_1_qlr[x] = (core_offset_o[1] + queue_id_o[1]);
    queues_output_2_qlr[x] = (core_offset_o[2] + queue_id_o[2]);
    queues_output_3_qlr[x] = (core_offset_o[3] + queue_id_o[3]);
  }
  //Rest of the stages uses xqueue push operationss
  for (uint32_t y = 1; y < (NUM_STAGE-1); ++y) {
    for (uint32_t x = 0; x < PE_PER_STAGE; ++x) {
      for (uint32_t i = 0; i < 4; ++i){
        idx_out       = shuffling_order[(y)*FFTLEN + x*4 + i];
        tile_id_o[i]  = tile_mapping[(y+1)*PE_PER_STAGE + idx_out/4];
        core_id_o[i]  = core_mapping[(y+1)*PE_PER_STAGE + idx_out/4];
        queue_id_o[i] = idx_out%4;

        tile_offset_o[i] = tile_id_o[i] * SEQ_MEM_SIZE;
        core_offset_o[i] = (core_id_o[i] % 4) * 4;
      }

      queues_output_0[y-1][x] = &__seq_start + tile_offset_o[0] + core_offset_o[0] + queue_id_o[0];
      queues_output_1[y-1][x] = &__seq_start + tile_offset_o[1] + core_offset_o[1] + queue_id_o[1];
      queues_output_2[y-1][x] = &__seq_start + tile_offset_o[2] + core_offset_o[2] + queue_id_o[2];
      queues_output_3[y-1][x] = &__seq_start + tile_offset_o[3] + core_offset_o[3] + queue_id_o[3];
    }
  }
}

//first fft stage
void systolic_first_fft_pe(uint32_t stage_idx, uint32_t idx_in_stage){
  volatile int32_t *qlr_cfg_t0 = (int32_t *)QLR_CFG_T0;
  volatile int32_t *qlr_cfg_t1 = (int32_t *)QLR_CFG_T1;
  volatile int32_t *qlr_cfg_t2 = (int32_t *)QLR_CFG_T2;
  volatile int32_t *qlr_cfg_t3 = (int32_t *)QLR_CFG_T3;

  int32_t reqs = NUM_ITER;
  //Configure QLRs
  qlr_cfg_t0[QLR_CFG_REQ] = (int32_t)reqs;
  qlr_cfg_t0[QLR_CFG_OADDR] = (int32_t)queues_output_0_qlr[idx_in_stage];
  qlr_cfg_t1[QLR_CFG_REQ] = (int32_t)reqs;
  qlr_cfg_t1[QLR_CFG_OADDR] = (int32_t)queues_output_1_qlr[idx_in_stage];
  qlr_cfg_t2[QLR_CFG_REQ] = (int32_t)reqs;
  qlr_cfg_t2[QLR_CFG_OADDR] = (int32_t)queues_output_2_qlr[idx_in_stage];
  qlr_cfg_t3[QLR_CFG_REQ] = (int32_t)reqs;
  qlr_cfg_t3[QLR_CFG_OADDR] = (int32_t)queues_output_3_qlr[idx_in_stage];

  //Start QLR
  qlr_cfg_t0[QLR_CFG_TYPE] = 2;
  qlr_cfg_t1[QLR_CFG_TYPE] = 2;
  qlr_cfg_t2[QLR_CFG_TYPE] = 2;
  qlr_cfg_t3[QLR_CFG_TYPE] = 2;

  int16_t t0, t1, t2;
  v2s A, B, C, D, E, F, G, H;
  //uint16_t i0,i1,i2,i3;
  //Digit-reverse order calcuation
  int16_t sum,temp,digit,i, j,i0[4];
  for (i=0;i<4;i++){
    sum = 0;
    temp = idx_in_stage*4 +i;
    for (j=0;j<NUM_STAGE;j++){
      digit = temp%4;
      sum = sum*4 + digit;
      temp = temp/4;
    }
    i0[i] = sum;
  }

  //Radix4 calculation
  v2s s2;
  asm volatile("addi %[s2], zero, 0x02;"
              "slli %[s2], %[s2], 0x10;"
              "addi %[s2], %[s2], 0x02;"
              :[s2] "=&r"(s2)
              :);
  int32_t* addr_0, addr_1, addr_2, addr_3;
  int32_t addr_incr, addr_decr;
  addr_0=&pSrc[(i0[0]*2U)];
  addr_1=&pSrc[(i0[1]*2U)];
  addr_2=&pSrc[(i0[2]*2U)];
  addr_3=&pSrc[(i0[3]*2U)];
  addr_incr = FFTLEN*4U;
  addr_decr = -3*FFTLEN*4U;
  //Unrolled loop for repeat over the 4 diffrent inputs
  for (i=0;i<NUM_ITER/4;i++){
    //post-increment loads
    asm volatile("p.lw %[A], %[addr_incr](%[addr_0]!);"
                "p.lw %[B], %[addr_incr](%[addr_1]!);"
                "p.lw %[C], %[addr_incr](%[addr_2]!);"
                "p.lw %[D], %[addr_incr](%[addr_3]!);"
                : [A] "=&r"(A), [B] "=&r"(B), [C] "=&r"(C), [D] "=&r"(D),
                [addr_0]"+&r"(addr_0),[addr_1]"+&r"(addr_1),
                [addr_2]"+&r"(addr_2),[addr_3]"+&r"(addr_3)
                :[addr_incr]"r"(addr_incr)
                );

    asm volatile("pv.sra.h  %[A],%[A],%[s2];"
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
                "pv.add.h  %[qlr_t0],%[E],%[G];"
                "pv.sub.h  %[qlr_t2],%[E],%[G];"
                "pv.sub.h  %[qlr_t1],%[F],%[A];"
                "pv.add.h  %[qlr_t3],%[A],%[F];"
                : [A] "+&r"(A), [B] "+&r"(B), [C] "+&r"(C), [D] "+&r"(D), [E] "=&r"(E),
                [F] "=&r"(F), [G] "=&r"(G), [H] "=&r"(H), [t0] "=&r"(t0),
                [t1] "=&r"(t1), [t2] "=&r"(t2), [qlr_t0] "+&r"(qlr_t0),
                [qlr_t1] "+&r"(qlr_t1), [qlr_t2] "+&r"(qlr_t2), [qlr_t3] "+&r"(qlr_t3)
                :[s2] "r"(s2)
                :);

    asm volatile("p.lw %[A], %[addr_incr](%[addr_0]!);"
                "p.lw %[B], %[addr_incr](%[addr_1]!);"
                "p.lw %[C], %[addr_incr](%[addr_2]!);"
                "p.lw %[D], %[addr_incr](%[addr_3]!);"
                : [A] "=&r"(A), [B] "=&r"(B), [C] "=&r"(C), [D] "=&r"(D),
                [addr_0]"+&r"(addr_0),[addr_1]"+&r"(addr_1),
                [addr_2]"+&r"(addr_2),[addr_3]"+&r"(addr_3)
                :[addr_incr]"r"(addr_incr)
                );

    asm volatile("pv.sra.h  %[A],%[A],%[s2];"
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
                "pv.add.h  %[qlr_t0],%[E],%[G];"
                "pv.sub.h  %[qlr_t2],%[E],%[G];"
                "pv.sub.h  %[qlr_t1],%[F],%[A];"
                "pv.add.h  %[qlr_t3],%[A],%[F];"
                : [A] "+&r"(A), [B] "+&r"(B), [C] "+&r"(C), [D] "+&r"(D), [E] "=&r"(E),
                [F] "=&r"(F), [G] "=&r"(G), [H] "=&r"(H), [t0] "=&r"(t0),
                [t1] "=&r"(t1), [t2] "=&r"(t2), [qlr_t0] "+&r"(qlr_t0),
                [qlr_t1] "+&r"(qlr_t1), [qlr_t2] "+&r"(qlr_t2), [qlr_t3] "+&r"(qlr_t3)
                :[s2] "r"(s2)
                :);

    asm volatile("p.lw %[A], %[addr_incr](%[addr_0]!);"
                "p.lw %[B], %[addr_incr](%[addr_1]!);"
                "p.lw %[C], %[addr_incr](%[addr_2]!);"
                "p.lw %[D], %[addr_incr](%[addr_3]!);"
                : [A] "=&r"(A), [B] "=&r"(B), [C] "=&r"(C), [D] "=&r"(D),
                [addr_0]"+&r"(addr_0),[addr_1]"+&r"(addr_1),
                [addr_2]"+&r"(addr_2),[addr_3]"+&r"(addr_3)
                :[addr_incr]"r"(addr_incr)
                );

    asm volatile("pv.sra.h  %[A],%[A],%[s2];"
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
                "pv.add.h  %[qlr_t0],%[E],%[G];"
                "pv.sub.h  %[qlr_t2],%[E],%[G];"
                "pv.sub.h  %[qlr_t1],%[F],%[A];"
                "pv.add.h  %[qlr_t3],%[A],%[F];"
                : [A] "+&r"(A), [B] "+&r"(B), [C] "+&r"(C), [D] "+&r"(D), [E] "=&r"(E),
                [F] "=&r"(F), [G] "=&r"(G), [H] "=&r"(H), [t0] "=&r"(t0),
                [t1] "=&r"(t1), [t2] "=&r"(t2), [qlr_t0] "+&r"(qlr_t0),
                [qlr_t1] "+&r"(qlr_t1), [qlr_t2] "+&r"(qlr_t2), [qlr_t3] "+&r"(qlr_t3)
                :[s2] "r"(s2)
                :);

    asm volatile("p.lw %[A], %[addr_decr](%[addr_0]!);"
                "p.lw %[B], %[addr_decr](%[addr_1]!);"
                "p.lw %[C], %[addr_decr](%[addr_2]!);"
                "p.lw %[D], %[addr_decr](%[addr_3]!);"
                : [A] "=&r"(A), [B] "=&r"(B), [C] "=&r"(C), [D] "=&r"(D),
                [addr_0]"+&r"(addr_0),[addr_1]"+&r"(addr_1),
                [addr_2]"+&r"(addr_2),[addr_3]"+&r"(addr_3)
                :[addr_decr]"r"(addr_decr)
                );

    asm volatile("pv.sra.h  %[A],%[A],%[s2];"
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
                "pv.add.h  %[qlr_t0],%[E],%[G];"
                "pv.sub.h  %[qlr_t2],%[E],%[G];"
                "pv.sub.h  %[qlr_t1],%[F],%[A];"
                "pv.add.h  %[qlr_t3],%[A],%[F];"
                : [A] "+&r"(A), [B] "+&r"(B), [C] "+&r"(C), [D] "+&r"(D), [E] "=&r"(E),
                [F] "=&r"(F), [G] "=&r"(G), [H] "=&r"(H), [t0] "=&r"(t0),
                [t1] "=&r"(t1), [t2] "=&r"(t2), [qlr_t0] "+&r"(qlr_t0),
                [qlr_t1] "+&r"(qlr_t1), [qlr_t2] "+&r"(qlr_t2), [qlr_t3] "+&r"(qlr_t3)
                :[s2] "r"(s2)
                :);
  }
}


//Middle stages

void systolic_mid_pe(uint32_t stage_idx, uint32_t idx_in_stage, uint32_t core_id){
  int32_t *queue_next_0;
  int32_t *queue_next_1;
  int32_t *queue_next_2;
  int32_t *queue_next_3;

  volatile int32_t *qlr_cfg_t0 = (int32_t *)QLR_CFG_T0;
  volatile int32_t *qlr_cfg_t1 = (int32_t *)QLR_CFG_T1;
  volatile int32_t *qlr_cfg_t2 = (int32_t *)QLR_CFG_T2;
  volatile int32_t *qlr_cfg_t3 = (int32_t *)QLR_CFG_T3;
  uint32_t core_offset = core_id * sizeof(int32_t);
  // Assign queues
  queue_next_0 = queues_output_0[stage_idx-1][idx_in_stage];
  queue_next_1 = queues_output_1[stage_idx-1][idx_in_stage];
  queue_next_2 = queues_output_2[stage_idx-1][idx_in_stage];
  queue_next_3 = queues_output_3[stage_idx-1][idx_in_stage];

  int32_t reqs = NUM_ITER;
  //Configure QLRs
  qlr_cfg_t0[QLR_CFG_REQ] = (int32_t)reqs;
  qlr_cfg_t0[QLR_CFG_IADDR] = (int32_t)(core_offset + 0);
  qlr_cfg_t0[QLR_CFG_RF] = (int32_t)1;
  qlr_cfg_t1[QLR_CFG_REQ] = (int32_t)reqs;
  qlr_cfg_t1[QLR_CFG_IADDR] = (int32_t)(core_offset + 1);
  qlr_cfg_t1[QLR_CFG_RF] = (int32_t)2;
  qlr_cfg_t2[QLR_CFG_REQ] = (int32_t)reqs;
  qlr_cfg_t2[QLR_CFG_IADDR] = (int32_t)(core_offset + 2);
  qlr_cfg_t2[QLR_CFG_RF] = (int32_t)2;
  qlr_cfg_t3[QLR_CFG_REQ] = (int32_t)reqs;
  qlr_cfg_t3[QLR_CFG_IADDR] = (int32_t)(core_offset + 3);
  qlr_cfg_t3[QLR_CFG_RF] = (int32_t)2;

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
  twiddle_multiplier = 1 <<(2*(NUM_STAGE-stage_idx-1));//4^(NUM_STAGE-stage_idx-1)

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
  //Needs to be calculated only once
  asm volatile("addi %[s1], zero, 0x01;"
              "slli %[s1], %[s1], 0x10;"
              "addi %[s1], %[s1], 0x01;"
              :[s1] "=&r"(s1)
              :);
  for(int32_t i=0;i<reqs;i++){

    asm volatile("pv.dotsp.h  %[E],%[CoSi1],%[qlr_t1];"
                "pv.dotsp.h  %[F],%[C1],%[qlr_t1];"
                "srai  %[t0],%[E],0x10;"
                "srai  %[t1],%[F],0x10;"
                "pv.pack %[B],%[t1],%[t0];"
                "pv.dotsp.h  %[E],%[CoSi3],%[qlr_t3];"
                "pv.dotsp.h  %[F],%[C3],%[qlr_t3];"
                "srai  %[t0],%[E],0x10;"
                "srai  %[t1],%[F],0x10;"
                "pv.pack %[D],%[t1],%[t0];"
                "pv.dotsp.h  %[G],%[CoSi2],%[qlr_t2];"
                "pv.dotsp.h  %[H],%[C2],%[qlr_t2];"
                "srai  %[t0],%[G],0x10;"
                "srai  %[t1],%[H],0x10;"
                "pv.pack %[C],%[t1],%[t0];"
                "pv.sra.h  %[A],%[qlr_t0],%[s1];"
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
                "sub %[t1],zero,%[t1];"
                "pv.pack %[A],%[t0],%[t1];"
                "pv.add.h  %[B],%[E],%[G];"
                "pv.sub.h  %[D],%[E],%[G];"
                "pv.sub.h  %[C],%[F],%[A];"
                "pv.add.h  %[H],%[A],%[F];"
                : [A] "=&r"(A), [B] "=&r"(B), [C] "=&r"(C), [D] "=&r"(D),
                  [E] "=&r"(E), [F] "=&r"(F), [G] "=&r"(G), [H] "=&r"(H),
                  [t0] "=&r"(t0), [t1] "=&r"(t1), [qlr_t0] "+&r"(qlr_t0),
                  [qlr_t1] "+&r"(qlr_t1), [qlr_t2] "+&r"(qlr_t2), [qlr_t3] "+&r"(qlr_t3)
                : [C1] "r"(C1), [C2] "r"(C2), [C3] "r"(C3), [CoSi1] "r"(CoSi1),
                  [CoSi2] "r"(CoSi2), [CoSi3] "r"(CoSi3), [s1] "r"(s1)
                :);

    //Push the results to the output queue
    asm volatile("q.push.w %[resp_0], %[B], (%[queue_next_0]);"
                "q.push.w %[resp_1], %[C], (%[queue_next_1]);"
                "q.push.w %[resp_2], %[D], (%[queue_next_2]);"
                "q.push.w %[resp_3], %[H], (%[queue_next_3]);"
                :[resp_0]"=rm"(resp_0),[resp_1]"=rm"(resp_1),
                [resp_2]"=rm"(resp_2),[resp_3]"=rm"(resp_3)
                :[B] "r"(B),[C] "r"(C),[D] "r"(D),[H] "r"(H),
                [queue_next_0] "r"(queue_next_0),[queue_next_1] "r"(queue_next_1),
                [queue_next_2] "r"(queue_next_2),[queue_next_3] "r"(queue_next_3));
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
  qlr_cfg_t0[QLR_CFG_RF] = (int32_t)1;
  qlr_cfg_t1[QLR_CFG_REQ] = (int32_t)reqs;
  qlr_cfg_t1[QLR_CFG_IADDR] = (int32_t)(core_offset + 1);
  qlr_cfg_t1[QLR_CFG_RF] = (int32_t)2;
  qlr_cfg_t2[QLR_CFG_REQ] = (int32_t)reqs;
  qlr_cfg_t2[QLR_CFG_IADDR] = (int32_t)(core_offset + 2);
  qlr_cfg_t2[QLR_CFG_RF] = (int32_t)2;
  qlr_cfg_t3[QLR_CFG_REQ] = (int32_t)reqs;
  qlr_cfg_t3[QLR_CFG_IADDR] = (int32_t)(core_offset + 3);
  qlr_cfg_t3[QLR_CFG_RF] = (int32_t)2;

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
  i0 = shuffling_order[3*FFTLEN + 4*idx_in_stage];
  i1 = shuffling_order[3*FFTLEN + 4*idx_in_stage + 1];
  i2 = shuffling_order[3*FFTLEN + 4*idx_in_stage + 2];
  i3 = shuffling_order[3*FFTLEN + 4*idx_in_stage + 3];
//Radix4 calculation
  v2s s1;
  //Needs to be calculated only once
  asm volatile("addi %[s1], zero, 0x01;"
              "slli %[s1], %[s1], 0x10;"
              "addi %[s1], %[s1], 0x01;"
              :[s1] "=&r"(s1)
              :);
  for(int32_t i=0;i<reqs;i++){
    asm volatile("pv.dotsp.h  %[E],%[CoSi1],%[qlr_t1];"
                "pv.dotsp.h  %[F],%[C1],%[qlr_t1];"
                "srai  %[t0],%[E],0x10;"
                "srai  %[t1],%[F],0x10;"
                "pv.pack %[B],%[t1],%[t0];"
                "pv.dotsp.h  %[E],%[CoSi3],%[qlr_t3];"
                "pv.dotsp.h  %[F],%[C3],%[qlr_t3];"
                "srai  %[t0],%[E],0x10;"
                "srai  %[t1],%[F],0x10;"
                "pv.pack %[D],%[t1],%[t0];"
                "pv.dotsp.h  %[G],%[CoSi2],%[qlr_t2];"
                "pv.dotsp.h  %[H],%[C2],%[qlr_t2];"
                "srai  %[t0],%[G],0x10;"
                "srai  %[t1],%[H],0x10;"
                "pv.pack %[C],%[t1],%[t0];"
                "pv.sra.h  %[A],%[qlr_t0],%[s1];"
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
                "sub %[t1],zero,%[t1];"
                "pv.pack %[A],%[t0],%[t1];"
                "pv.add.h  %[B],%[E],%[G];"
                "pv.sub.h  %[D],%[E],%[G];"
                "pv.sub.h  %[C],%[F],%[A];"
                "pv.add.h  %[H],%[A],%[F];"
                : [A] "=&r"(A), [B] "=&r"(B), [C] "=&r"(C), [D] "=&r"(D),
                  [E] "=&r"(E), [F] "=&r"(F), [G] "=&r"(G), [H] "=&r"(H),
                  [t0] "=&r"(t0), [t1] "=&r"(t1), [qlr_t0] "+&r"(qlr_t0),
                  [qlr_t1] "+&r"(qlr_t1), [qlr_t2] "+&r"(qlr_t2), [qlr_t3] "+&r"(qlr_t3)
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
