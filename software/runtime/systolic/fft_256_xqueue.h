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
//         Sergio Mazzola, ETH Zurich

/*
 * Intial, systolic implementation of 256-point radix-4 DIT complex FFT. The cluster is partitioned into 4
 * stages of 64 PEs each, interconnected in a radix-4 butterfly. DIT is used, where crambling in bitreversal
 * order is at the input (first stage).
 * First stage's PEs load the 256 input elements (4 per PE) and use Xqueue extension to push them through
 * the butterfly systolic array. A formulaic implementation is used for the shuffled output addresses
 * calculation.
 *
 * The stages of the systolic butterfly allow up to 4 FFTs to be executed at the same time in a pipelined
 * fashion, with each 64-PE stage processing a different FFT at that stage. With the same PES always processing
 * a different FFT in the same stage, the twiddle factor do not need to be re-loaded: always the same ones are
 * used. Also output addresses are computed once at the beginning and fixed for the whole computation.
 * For performance benchmarking at steady state, when the systolic array is completely full, the same FFT is
 * processed for NUM_REPS times. Set NUM_REPS to 1 to disable this feature for normal execution.
 */

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
#define NUM_REPS     150                        // repeat the same FFT multiple times, for benchmarking
//TODO: Check whether performance changes if repeating NUM_REPS/4 times but with 4 different FFTs in each iteration

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

extern int16_t vector_input[2 * LEN_FFT];
extern int16_t vector_output[2 * LEN_FFT];

// Shuffle the input points to stage_i, according to RADIX
void input_shuffling_order_r4(uint32_t stage_i, uint16_t* order){
  // The points are shuffled individually over the whole LEN_FFT, not considering that every
  // PE processes RADIX points (this will be considered later, in the queues assignment)

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

// Map the values of 'order' to their indices
void invert_shuffling_order(uint16_t* order, uint16_t* reverse_order){
  // reverse_order[order[i]] = i
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
  uint32_t tile_id_out[NUM_QUEUES_PER_CORE], core_id_out[NUM_QUEUES_PER_CORE], queue_id_out[NUM_QUEUES_PER_CORE];
  uint32_t tile_offset[NUM_QUEUES_PER_CORE], core_offset[NUM_QUEUES_PER_CORE], queue_offset[NUM_QUEUES_PER_CORE];

  // Compute output PEs for all stages, but the last one
  if (stage_i < (NUM_STAGES - 1)) {
    // Each PE has 4 outputs: make them correspond to the 4 available queues of each PE
    for (uint32_t i = 0; i < RADIX; i++){
      index_out = shuffling_order[stage_i][(pe_i * RADIX) + i];
      core_id_out[i]  = core_mapping[stage_i + 1][index_out / RADIX];
      tile_id_out[i]  = core_id_out[i] / NUM_CORES_PER_TILE;
      queue_id_out[i] = index_out % RADIX; // index_out % NUM_QUEUES_PER_CORE

      // base address of this tile's sequential memory region
      tile_offset[i] = tile_id_out[i] * NUM_CORES_PER_TILE * SEQ_MEM_SIZE;
      // next address goes to next bank, then wrap around tile sequential region
      core_offset[i] = (core_id_out[i] % NUM_CORES_PER_TILE) * NUM_QUEUES_PER_CORE * sizeof(int32_t);
      // each PE has 4 outputs, same number as queues: decide which out queue must be fed with output i
      queue_offset[i] = queue_id_out[i] * sizeof(int32_t);
    }

    // Output queues (for usage with Xqueue, so physical addresses)
    queues_out_0[stage_i][pe_i] = (uint32_t*)((uint32_t)(&__seq_start) + tile_offset[0] + core_offset[0] + queue_offset[0]);
    queues_out_1[stage_i][pe_i] = (uint32_t*)((uint32_t)(&__seq_start) + tile_offset[1] + core_offset[1] + queue_offset[1]);
    queues_out_2[stage_i][pe_i] = (uint32_t*)((uint32_t)(&__seq_start) + tile_offset[2] + core_offset[2] + queue_offset[2]);
    queues_out_3[stage_i][pe_i] = (uint32_t*)((uint32_t)(&__seq_start) + tile_offset[3] + core_offset[3] + queue_offset[3]);
  }
}


/*
 * First FFT stage
 *
 * Get inputs from memory and push to stage 2 through Xqueue.
 * 'pe_i' is the PE index in the current stage (0 to LEN_FFT/NUM_STAGES-1).
 */
void systolic_first_fft_pe(uint32_t pe_i){
  /* Configure input address */
  register int32_t input_base[RADIX];
  // Compute base addresses for vector_input of first stage
  for (uint32_t i = 0; i < RADIX; i++){
    int16_t sum = 0;
    int16_t temp = (int16_t)(pe_i * RADIX + i);
    for (uint32_t j = 0; j < NUM_STAGES; j++){
      int16_t digit = temp % RADIX;
      sum = (int16_t)(sum * RADIX + digit);
      temp = temp / RADIX;
    }
    // hack to cope with input_base's 'register' specifier (index must be hardcoded)
    // it is better to use 'register' so that the array is not stored in the stack, slowing
    // down the A, B, C, D FFT input loading due to address retrieval from stack
    switch (i) {
      case 0:
        input_base[0] = sum;
        break;
      case 1:
        input_base[1] = sum;
        break;
      case 2:
        input_base[2] = sum;
        break;
      case 3:
        input_base[3] = sum;
        break;
      default:
        printf("Error: wrong radix\n");
        return;
    }
  }

  /* Configure Xqueue */
  // Assign output queues (Xqueue)
  uint32_t *queue_next_0 = queues_out_0[0][pe_i];
  uint32_t *queue_next_1 = queues_out_1[0][pe_i];
  uint32_t *queue_next_2 = queues_out_2[0][pe_i];
  uint32_t *queue_next_3 = queues_out_3[0][pe_i];
  // Xqueue response
  int32_t resp_0 __attribute__((unused)) = 0;
  int32_t resp_1 __attribute__((unused)) = 0;
  int32_t resp_2 __attribute__((unused)) = 0;
  int32_t resp_3 __attribute__((unused)) = 0;

  /* Preparation */
  // radix-4 calculation constant (mult by 4 with right shift)
  v2s shift_2 = (v2s){0x0002, 0x0002};

  /* Load inputs and compute FFT */
  v2s A, B, C, D, E, F, G, H;
  int16_t t0, t1, t2;

  for (uint32_t i = 0; i < NUM_REPS; i++) {
    //TODO: Verify that this is actually done at every iteration (maybe set volatile?)
    // Load input
    A = ((v2s*)&vector_input)[input_base[0]];
    B = ((v2s*)&vector_input)[input_base[1]];
    C = ((v2s*)&vector_input)[input_base[2]];
    D = ((v2s*)&vector_input)[input_base[3]];

    // Compute FFT
    __asm__ volatile (
      "pv.sra.h     %[A],%[A],%[shift_2] \n\t"
      "pv.sra.h     %[C],%[C],%[shift_2] \n\t"
      "pv.sra.h     %[B],%[B],%[shift_2] \n\t"
      "pv.sra.h     %[D],%[D],%[shift_2] \n\t"
      "pv.add.h     %[E],%[A],%[C]       \n\t"
      "pv.sub.h     %[F],%[A],%[C]       \n\t"
      "pv.sub.h     %[H],%[B],%[D]       \n\t"
      "pv.add.h     %[G],%[B],%[D]       \n\t"
      "pv.extract.h %[t0],%[H],0         \n\t"
      "pv.extract.h %[t1],%[H],1         \n\t"
      "sub          %[t2],zero,%[t1]     \n\t"
      "pv.pack      %[A],%[t0],%[t2]     \n\t"
      "pv.add.h     %[B],%[E],%[G]       \n\t"
      "pv.sub.h     %[D],%[E],%[G]       \n\t"
      "pv.sub.h     %[C],%[F],%[A]       \n\t"
      "pv.add.h     %[H],%[A],%[F]       \n\t"
      : [A] "+&r"(A), [B] "+&r"(B), [C] "+&r"(C), [D] "+&r"(D),
        [E] "=&r"(E), [F] "=&r"(F), [G] "=&r"(G), [H] "=&r"(H),
        [t0] "=&r"(t0), [t1] "=&r"(t1), [t2] "=&r"(t2)
      : [shift_2] "r"(shift_2) :
    );

    // Push the results to the output queue (Xqueue)
    queue_push(queue_next_0, (int32_t)B, &resp_0);
    queue_push(queue_next_1, (int32_t)C, &resp_1);
    queue_push(queue_next_2, (int32_t)D, &resp_2);
    queue_push(queue_next_3, (int32_t)H, &resp_3);
  }
}


// QLR CSR addresses
#define INNER_PE_DEFINE_QLR_CONFIG                        \
  volatile uint32_t *qlr_cfg_t0 = (uint32_t *)QLR_CFG_T0; \
  volatile uint32_t *qlr_cfg_t1 = (uint32_t *)QLR_CFG_T1; \
  volatile uint32_t *qlr_cfg_t2 = (uint32_t *)QLR_CFG_T2; \
  volatile uint32_t *qlr_cfg_t3 = (uint32_t *)QLR_CFG_T3

#define INNER_PE_CONFIG_QLR                      \
  do {                                           \
    qlr_cfg_t0[QLR_CFG_REQ] = NUM_REPS;          \
    qlr_cfg_t0[QLR_CFG_IADDR] = core_offset + 0; \
    qlr_cfg_t1[QLR_CFG_REQ] = NUM_REPS;          \
    qlr_cfg_t1[QLR_CFG_IADDR] = core_offset + 1; \
    qlr_cfg_t2[QLR_CFG_REQ] = NUM_REPS;          \
    qlr_cfg_t2[QLR_CFG_IADDR] = core_offset + 2; \
    qlr_cfg_t3[QLR_CFG_REQ] = NUM_REPS;          \
    qlr_cfg_t3[QLR_CFG_IADDR] = core_offset + 3; \
  } while (0)

#define INNER_PE_COMPUTE_TWIDFACT                                    \
  v2s CoSi1 = ((v2s*)&twiddleCoef_q16)[ic * 1];                      \
  v2s CoSi2 = ((v2s*)&twiddleCoef_q16)[ic * 2];                      \
  v2s CoSi3 = ((v2s*)&twiddleCoef_q16)[ic * 3];                      \
                                                                     \
  /* Prepare 16-bit twiddle factors */                               \
  __asm__ volatile (                                                 \
    "pv.extract.h  %[t1],%[CoSi1],0  \n\t"                           \
    "pv.extract.h  %[t3],%[CoSi2],0  \n\t"                           \
    "pv.extract.h  %[t5],%[CoSi3],0  \n\t"                           \
    "pv.extract.h  %[t0],%[CoSi1],1  \n\t"                           \
    "pv.extract.h  %[t2],%[CoSi2],1  \n\t"                           \
    "pv.extract.h  %[t4],%[CoSi3],1  \n\t"                           \
    "sub           %[t0],zero,%[t0]  \n\t"                           \
    "sub           %[t2],zero,%[t2]  \n\t"                           \
    "sub           %[t4],zero,%[t4]  \n\t"                           \
    "pv.pack       %[C1],%[t1],%[t0] \n\t"                           \
    "pv.pack       %[C2],%[t3],%[t2] \n\t"                           \
    "pv.pack       %[C3],%[t5],%[t4] \n\t"                           \
    : [C1] "=r"(C1), [C2] "=r"(C2), [C3] "=r"(C3),                   \
      [t0] "=&r"(t0), [t1] "=&r"(t1), [t2] "=&r"(t2),                \
      [t3] "=&r"(t3), [t4] "=&r"(t4), [t5] "=&r"(t5)                 \
    : [CoSi1] "r"(CoSi1), [CoSi2] "r"(CoSi2), [CoSi3] "r"(CoSi3) :   \
  )

#define INNER_PE_FFT_COMPUTATION                                                      \
__asm__ __volatile__("" : "=r"(qlr_t0), "=r"(qlr_t1),"=r"(qlr_t2),"=r"(qlr_t3));      \
                                                                                      \
  /*TODO: This can be optimized by exploiting the number of requests instead of mv */ \
  B = (v2s)qlr_t1;                                                                    \
  D = (v2s)qlr_t3;                                                                    \
  A = (v2s)qlr_t0;                                                                    \
  C = (v2s)qlr_t2;                                                                    \
                                                                                      \
  /* Compute FFT */                                                                   \
  __asm__ volatile (                                                                  \
    "pv.dotsp.h   %[E],%[CoSi1],%[B]   \n\t"                                          \
    "pv.dotsp.h   %[F],%[C1],%[B]      \n\t"                                          \
    "pv.dotsp.h   %[G],%[CoSi2],%[C]   \n\t"                                          \
    "pv.dotsp.h   %[H],%[C2],%[C]      \n\t"                                          \
    "srai         %[t0],%[E],0x10      \n\t"                                          \
    "srai         %[t1],%[F],0x10      \n\t"                                          \
    "pv.dotsp.h   %[E],%[CoSi3],%[D]   \n\t"                                          \
    "pv.dotsp.h   %[F],%[C3],%[D]      \n\t"                                          \
    "srai         %[t2],%[G],0x10      \n\t"                                          \
    "srai         %[t3],%[H],0x10      \n\t"                                          \
    "srai         %[t4],%[E],0x10      \n\t"                                          \
    "srai         %[t5],%[F],0x10      \n\t"                                          \
    "pv.pack      %[B],%[t1],%[t0]     \n\t"                                          \
    "pv.pack      %[D],%[t5],%[t4]     \n\t"                                          \
    "pv.pack      %[C],%[t3],%[t2]     \n\t"                                          \
    "pv.sra.h     %[A],%[A],%[shift_1] \n\t"                                          \
    "pv.sub.h     %[H],%[B],%[D]       \n\t"                                          \
    "pv.add.h     %[E],%[A],%[C]       \n\t"                                          \
    "pv.sub.h     %[F],%[A],%[C]       \n\t"                                          \
    "pv.sra.h     %[H],%[H],%[shift_1] \n\t"                                          \
    "pv.add.h     %[G],%[B],%[D]       \n\t"                                          \
    "pv.sra.h     %[E],%[E],%[shift_1] \n\t"                                          \
    "pv.extract.h %[t0],%[H],0         \n\t"                                          \
    "pv.extract.h %[t1],%[H],1         \n\t"                                          \
    "pv.sra.h     %[F],%[F],%[shift_1] \n\t"                                          \
    "pv.sra.h     %[G],%[G],%[shift_1] \n\t"                                          \
    "sub          %[t2],zero,%[t1]     \n\t"                                          \
    "pv.pack      %[A],%[t0],%[t2]     \n\t"                                          \
    "pv.add.h     %[B],%[E],%[G]       \n\t"                                          \
    "pv.sub.h     %[D],%[E],%[G]       \n\t"                                          \
    "pv.sub.h     %[C],%[F],%[A]       \n\t"                                          \
    "pv.add.h     %[H],%[A],%[F]       \n\t"                                          \
    : [A] "+&r"(A), [B] "+&r"(B), [C] "+&r"(C), [D] "+&r"(D),                         \
      [E] "=&r"(E), [F] "=&r"(F), [G] "=&r"(G), [H] "=&r"(H),                         \
      [t0] "=&r"(t0), [t1] "=&r"(t1), [t2] "=&r"(t2),                                 \
      [t3] "=&r"(t3), [t4] "=&r"(t4), [t5] "=&r"(t5)                                  \
    : [C1] "r"(C1), [C2] "r"(C2), [C3] "r"(C3), [shift_1] "r"(shift_1),               \
      [CoSi1] "r"(CoSi1), [CoSi2] "r"(CoSi2), [CoSi3] "r"(CoSi3) :                    \
  )


/*
 * Middle FFT stage
 *
 * Pop points from previous stage through QLRs, compute FFT, and push to
 * next stage through Xqueue.
 * 'stage_i' is the stage index (0 to NUM_STAGES-1),
 * 'pe_i' is the PE index in the current stage (0 to LEN_FFT/NUM_STAGES-1)
 */
void systolic_mid_pe(uint32_t stage_i, uint32_t pe_i, uint32_t core_id){
  /* Configure QLRs */
  INNER_PE_DEFINE_QLR_CONFIG;
  // Base address (ID only) for the memory banks (queues) of this core
  uint32_t core_offset = core_id * NUM_QUEUES_PER_CORE;

  INNER_PE_CONFIG_QLR;

  /* Configure Xqueue */
  // Assign output queues (Xqueue)
  uint32_t *queue_next_0 = queues_out_0[stage_i][pe_i];
  uint32_t *queue_next_1 = queues_out_1[stage_i][pe_i];
  uint32_t *queue_next_2 = queues_out_2[stage_i][pe_i];
  uint32_t *queue_next_3 = queues_out_3[stage_i][pe_i];
  // Xqueue response
  int32_t resp_0 __attribute__((unused)) = 0;
  int32_t resp_1 __attribute__((unused)) = 0;
  int32_t resp_2 __attribute__((unused)) = 0;
  int32_t resp_3 __attribute__((unused)) = 0;

  /* Twiddle coefficients calculation */
  v2s C1, C2, C3;
  int16_t t0, t1, t2, t3, t4, t5;

  uint32_t nvar_group_by_4 = (uint32_t)1 << (2 * (stage_i));
  uint32_t twiddle_multiplier = (uint32_t)1 << (2 * (NUM_STAGES - (stage_i + 1)));
  uint32_t ic = (pe_i % nvar_group_by_4) * twiddle_multiplier;

  INNER_PE_COMPUTE_TWIDFACT;

  /* Preparation */
  // radix-4 calculation constant (mult by 2 with right shift)
  v2s shift_1 = (v2s){0x0001, 0x0001};

  /* Compute FFT */
  v2s A, B, C, D, E, F, G, H;

  // Start QLR
  qlr_cfg_t0[QLR_CFG_TYPE] = QLR_TYPE_IQLR;
  qlr_cfg_t1[QLR_CFG_TYPE] = QLR_TYPE_IQLR;
  qlr_cfg_t2[QLR_CFG_TYPE] = QLR_TYPE_IQLR;
  qlr_cfg_t3[QLR_CFG_TYPE] = QLR_TYPE_IQLR;

  for (uint32_t i = 0; i < NUM_REPS; i++) {
    INNER_PE_FFT_COMPUTATION;
    // Push the results to the output queue (Xqueue)
    queue_push(queue_next_0, (int32_t)B, &resp_0);
    queue_push(queue_next_1, (int32_t)C, &resp_1);
    queue_push(queue_next_2, (int32_t)D, &resp_2);
    queue_push(queue_next_3, (int32_t)H, &resp_3);
  }
}

/*
 * Last FFT stage
 *
 * Pop points from previous stage through QLRs and compute FFT output
 * 'pe_i' is the PE index in the current stage (0 to LEN_FFT/NUM_STAGES-1)
 */
void systolic_end_pe(uint32_t pe_i, uint32_t core_id){
  /* Configure QLRs */
  INNER_PE_DEFINE_QLR_CONFIG;
  // Base address (ID only) for the memory banks (queues) of this core
  uint32_t core_offset = core_id * NUM_QUEUES_PER_CORE;

  INNER_PE_CONFIG_QLR;

  /* Configure output address */
  uint32_t output_base[RADIX];
  for (uint32_t i = 0; i < RADIX; i++) {
    output_base[i] = shuffling_order[NUM_STAGES - 1][RADIX * pe_i + i];
  }

  /* Twiddle coefficients calculation */
  v2s C1, C2, C3;
  int16_t t0, t1, t2, t3, t4, t5;

  uint32_t ic = pe_i;

  INNER_PE_COMPUTE_TWIDFACT;

  /* Preparation */
  // radix-4 calculation constant (mult by 2 with right shift)
  v2s shift_1 = (v2s){0x0001, 0x0001};

  /* Compute FFT */
  v2s A, B, C, D, E, F, G, H;

  // Start QLR
  qlr_cfg_t0[QLR_CFG_TYPE] = QLR_TYPE_IQLR;
  qlr_cfg_t1[QLR_CFG_TYPE] = QLR_TYPE_IQLR;
  qlr_cfg_t2[QLR_CFG_TYPE] = QLR_TYPE_IQLR;
  qlr_cfg_t3[QLR_CFG_TYPE] = QLR_TYPE_IQLR;

  for (uint32_t i = 0; i < NUM_REPS; i++) {
    INNER_PE_FFT_COMPUTATION;
    // Store the results to the output vector
    ((int32_t*)&vector_output)[output_base[0]] = (int32_t)B;
    ((int32_t*)&vector_output)[output_base[1]] = (int32_t)C;
    ((int32_t*)&vector_output)[output_base[2]] = (int32_t)D;
    ((int32_t*)&vector_output)[output_base[3]] = (int32_t)H;
  }
}
