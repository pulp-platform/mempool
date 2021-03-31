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

// Author: Gua Hao Khov, ETH Zurich

/* This library implements a simple systolic architecture emulation
 * using central instruction based orchestration
 */

#include "alloc.h"
#include "printf.h"

// Size of systolic array
#define SYSTOLIC_SIZE 3

// Size of all queues
#define QUEUE_SIZE 5

// Instruction Codes
#define INSTR_NOP 0
#define INSTR_RESET 1
#define INSTR_MATRIX_MUL 2
#define INSTR_END 3
#define INSTR_KILL 4

// Array of queue ptrs in row-major order
queue_t *queues_down[NUM_CORES - 1][NUM_CORES];
queue_t *queues_right[NUM_CORES][NUM_CORES - 1];

void systolic_init() {
  for (uint32_t y = 0; y < NUM_CORES - 1; ++y) {
    for (uint32_t x = 0; x < NUM_CORES; ++x) {
      queue_create(&queues_down[y][x], QUEUE_SIZE);
    }
  }
  for (uint32_t y = 0; y < NUM_CORES; ++y) {
    for (uint32_t x = 0; x < NUM_CORES - 1; ++x) {
      queue_create(&queues_right[y][x], QUEUE_SIZE);
    }
  }
}

/* A is an M x N matrix, B is a N x P matrix, and C is a M x P matrix
 * C = AB (currently only support multiples of SYSTOLIC_SIZE?)
 */
void systolic_matrix_mul(int32_t const *__restrict__ A,
                         int32_t const *__restrict__ B, int32_t *__restrict__ C,
                         uint32_t M, uint32_t N, uint32_t P) {
  // TODO: IMPLEMENTATION
}

void systolic_column_ctrl(const uint32_t idx) {
  uint8_t loop = 1;
  queue_t *queue_prev;
  queue_t *queue_next;
  queue_t *queue_data;
  int32_t instr;
  uint16_t instr_code;
  uint16_t instr_rep;
  int32_t *return_ptr;
  int32_t *arg_ptr;
  int32_t data;

  // Assign queues
  queue_prev = queues_right[0][idx - 1];
  queue_next = queues_right[0][idx];
  queue_data = queues_down[0][idx];

  // Pre-fill queues
  data = INSTR_NOP;
  for (uint32_t i = 0; i < idx - 1; ++i) {
    while (queue_push(queue_data, &data)) {
    };
  }

  // Systolic loop
  while (loop) {
    // Receive instruction and instr_repetition count
    while (queue_pop(queue_prev, &instr)) {
    };
    instr_rep = (uint16_t)(instr >> 16);
    instr_code = instr & 0xFFFF;

    switch (instr_code) {
    case INSTR_NOP:
      while (queue_push(queue_next, &instr)) {
      };
      while (queue_push(queue_data, &instr)) {
      };
      break;

    case INSTR_RESET:
      while (queue_pop(queue_prev, (int32_t *)&return_ptr)) {
      };
      while (queue_push(queue_next, &instr)) {
      };
      while (queue_push(queue_next, (int32_t *)&return_ptr)) {
      };
      while (queue_push(queue_data, (int32_t *)&return_ptr)) {
      };
      break;

    case INSTR_MATRIX_MUL:
      while (queue_pop(queue_prev, (int32_t *)&return_ptr)) {
      };
      while (queue_push(queue_next, &instr)) {
      };
      while (queue_push(queue_next, (int32_t *)&return_ptr)) {
      };
      while (queue_push(queue_data, (int32_t *)&return_ptr)) {
      };
      for (uint32_t i = 0; i < instr_rep; ++i) {
        while (queue_pop(queue_prev, (int32_t *)&arg_ptr)) {
        };
        while (queue_push(queue_next, (int32_t *)&arg_ptr)) {
        };
        uint32_t offset;
        for (uint32_t y = 0; y < SYSTOLIC_SIZE; ++y) {
          offset = y * SYSTOLIC_SIZE + idx - 1;
          while (queue_push(queue_data, (arg_ptr + offset))) {
          };
        }
      }
      break;

    case INSTR_END:
      while (queue_pop(queue_prev, (int32_t *)&return_ptr)) {
      };
      while (queue_push(queue_next, &instr)) {
      };
      while (queue_push(queue_next, (int32_t *)&return_ptr)) {
      };
      while (queue_push(queue_data, (int32_t *)&return_ptr)) {
      };
      break;

    case INSTR_KILL:
      while (queue_push(queue_next, &instr)) {
      };
      while (queue_push(queue_data, &instr)) {
      };
      loop = 0;
      break;

    default:
      printf("Invalid instruction at CC%02u\n", idx);
    }
  }
}

void systolic_row_ctrl(const uint32_t idx) {
  uint8_t loop = 1;
  queue_t *queue_prev;
  queue_t *queue_next;
  queue_t *queue_data;
  int32_t instr;
  uint16_t instr_code;
  uint16_t instr_rep;
  int32_t *return_ptr;
  int32_t *arg_ptr;
  int32_t data;

  // Assign queues
  queue_prev = queues_down[idx - 1][0];
  queue_next = queues_down[idx][0];
  queue_data = queues_right[idx][0];

  // Pre-fill queues
  data = INSTR_NOP;
  for (uint32_t i = 0; i < idx - 1; ++i) {
    while (queue_push(queue_data, &data)) {
    };
  }

  // Systolic loop
  while (loop) {
    // Receive instruction and instr_repetition count
    while (queue_pop(queue_prev, &instr)) {
    };
    instr_rep = (uint16_t)(instr >> 16);
    instr_code = instr & 0xFFFF;

    switch (instr_code) {
    case INSTR_NOP:
      while (queue_push(queue_next, &instr)) {
      };
      while (queue_push(queue_data, &instr)) {
      };
      break;

    case INSTR_RESET:
      while (queue_pop(queue_prev, (int32_t *)&return_ptr)) {
      };
      while (queue_push(queue_next, &instr)) {
      };
      while (queue_push(queue_next, (int32_t *)&return_ptr)) {
      };
      while (queue_push(queue_data, &instr)) {
      };
      break;

    case INSTR_MATRIX_MUL:
      while (queue_pop(queue_prev, (int32_t *)&return_ptr)) {
      };
      while (queue_push(queue_next, &instr)) {
      };
      while (queue_push(queue_next, (int32_t *)&return_ptr)) {
      };
      while (queue_push(queue_data, &instr)) {
      };
      for (uint32_t i = 0; i < instr_rep; ++i) {
        while (queue_pop(queue_prev, (int32_t *)&arg_ptr)) {
        };
        while (queue_push(queue_next, (int32_t *)&arg_ptr)) {
        };
        uint32_t offset;
        for (uint32_t x = 0; x < SYSTOLIC_SIZE; ++x) {
          offset = (idx - 1) * SYSTOLIC_SIZE + x;
          while (queue_push(queue_data, (arg_ptr + offset))) {
          };
        }
      }
      break;

    case INSTR_END:
      while (queue_pop(queue_prev, (int32_t *)&return_ptr)) {
      };
      while (queue_push(queue_next, &instr)) {
      };
      while (queue_push(queue_next, (int32_t *)&return_ptr)) {
      };
      while (queue_push(queue_data, &instr)) {
      };
      break;

    case INSTR_KILL:
      while (queue_push(queue_next, &instr)) {
      };
      while (queue_push(queue_data, &instr)) {
      };
      loop = 0;
      break;

    default:
      printf("Invalid instruction at RC%02u\n", idx);
    }
  }
}

void systolic_proc_element(const uint32_t row_idx, const uint32_t col_idx) {
  uint8_t loop = 1;
  uint32_t data_row_idx = row_idx - 1;
  uint32_t data_col_idx = col_idx - 1;
  queue_t *queue_prev_horz;
  queue_t *queue_prev_vert;
  queue_t *queue_next_horz;
  queue_t *queue_next_vert;
  int32_t instr;
  uint16_t instr_code;
  uint16_t instr_rep;
  int32_t *return_ptr;
  int32_t data_horz;
  int32_t data_vert;
  uint32_t offset;

  // Assign queues
  queue_prev_horz = queues_right[row_idx - 1][col_idx - 1];
  queue_prev_vert = queues_down[row_idx - 1][col_idx - 1];
  queue_next_horz = queues_right[row_idx][col_idx];
  queue_next_vert = queues_down[row_idx][col_idx];

  // Systolic loop
  while (loop) {
    // Receive instruction and instr_repetition count
    while (queue_pop(queue_prev_horz, &instr)) {
    };
  }
  while (queue_pop(queue_prev_vert, (int32_t *)&return_ptr)) {
  };
  instr_rep = (uint16_t)(instr >> 16);
  instr_code = instr & 0xFFFF;

  switch (instr_code) {
  case INSTR_NOP:
    while (queue_push(queue_next_horz, &instr)) {
    };
    while (queue_push(queue_next_vert, (int32_t *)&return_ptr)) {
    };
    break;

  case INSTR_RESET:
    offset = data_row_idx * SYSTOLIC_SIZE + data_col_idx;
    *(return_ptr + offset) = 0;
    while (queue_push(queue_next_horz, &instr)) {
    };
    while (queue_push(queue_next_vert, (int32_t *)&return_ptr)) {
    };
    break;

  case INSTR_MATRIX_MUL:
    while (queue_push(queue_next_horz, &instr)) {
    };
    while (queue_push(queue_next_vert, (int32_t *)&return_ptr)) {
    };
    for (uint32_t i = 0; i < instr_rep; ++i) {
      for (uint32_t k = 0; k < SYSTOLIC_SIZE; ++k) {
        while (queue_pop(queue_prev_horz, &data_horz)) {
        };
        while (queue_pop(queue_prev_vert, &data_vert)) {
        };
        offset = data_row_idx * SYSTOLIC_SIZE + data_col_idx;
        *(return_ptr + offset) += data_horz * data_vert;
        while (queue_push(queue_next_horz, &data_horz)) {
        };
        while (queue_push(queue_next_vert, &data_vert)) {
        };
      }
    }
    break;

  case INSTR_END:
    if ((row_idx == SYSTOLIC_SIZE) && (col_idx == SYSTOLIC_SIZE)) {
      *return_ptr = 1;
    }
    while (queue_push(queue_next_horz, &instr)) {
    };
    while (queue_push(queue_next_vert, (int32_t *)&return_ptr)) {
    };
    break;

  case INSTR_KILL:
    while (queue_push(queue_next_horz, &instr)) {
    };
    while (queue_push(queue_next_vert, (int32_t *)&return_ptr)) {
    };
    loop = 0;
    break;

  default:
    printf("Invalid instruction at PE(%02u,%02u)\n", row_idx, col_idx);
  }
}
