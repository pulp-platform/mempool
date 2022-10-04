// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#include "xpulp/builtins_v2.h"
#include <stdio.h>
#include <stdlib.h>

#define FIXED_POINT 10
#define HALF 1023

void init_matrix(int32_t *matrix, uint32_t num_rows, uint32_t num_columns,
                 uint32_t core_id);
void init_matrix_zeros(int32_t *matrix, uint32_t num_rows, uint32_t num_columns,
                       uint32_t core_id);

void init_matrix(int32_t *matrix, uint32_t num_rows, uint32_t num_columns,
                 uint32_t core_id) {
  int16_t Re;
  int16_t Im;
  int32_t upper = -32768, lower = 32768;
  if (core_id == 0) {
    for (uint32_t i = 0; i < num_rows; i++) {
      for (uint32_t j = 0; j < num_columns; j++) {
        if (i == j) {
          matrix[i * num_rows + j] = (rand() % (upper - lower + 1)) + lower;
        } else {
          Re = (int16_t)((rand() % (upper - lower + 1)) + lower);
          Im = (int16_t)((rand() % (upper - lower + 1)) + lower);
          *(v2s *)&matrix[i * num_rows + j] = (v2s){Re, Im};
        }
      }
    }
  }
}

void init_matrix_zeros(int32_t *matrix, uint32_t num_rows, uint32_t num_columns,
                       uint32_t core_id) {
  if (core_id == 0) {
    for (uint32_t i = 0; i < num_columns; i++) {
      for (uint32_t j = 0; j < num_rows; j++) {
        matrix[j * num_columns + i] = 0;
      }
    }
  }
}
