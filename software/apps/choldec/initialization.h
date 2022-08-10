// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#define FIXED_POINT 16
#define FIX_DIV(a,b) ((int32_t)((a << FIXED_POINT) / b))
#define FIX_MUL(a,b) ((int32_t)((a * b) >> FIXED_POINT))
#define ABS(a) (a > 0 ? a : -a)

void display(int32_t *matrix, uint32_t num_rows, uint32_t num_columns);
void init_matrix(int32_t  *matrix, uint32_t num_rows, uint32_t num_columns, int32_t a, int32_t b, int32_t c, uint32_t core_id);
void init_matrix_zeros(int32_t  *matrix, uint32_t num_rows, uint32_t num_columns, uint32_t core_id);

void display(int32_t *matrix, uint32_t num_rows, uint32_t num_columns) {
    uint32_t i;
    for (i = 0; i < num_rows * num_columns; i++) {
      printf("Output[%d] = %8d\n", i, matrix[i]);
    }
}

void init_matrix(int32_t  *matrix, uint32_t num_rows, uint32_t num_columns, int32_t a, int32_t b, int32_t c, uint32_t core_id) {
  if(core_id == 0) {
    for(uint32_t j = 0; j < num_rows; j++) {
      for(uint32_t i = 0; i < num_columns; i++) {
          matrix[j * num_columns + i] = a * (int32_t)i + b * (int32_t)j + c;
      }
    }
  }
}

void init_matrix_zeros (int32_t  *matrix, uint32_t num_rows, uint32_t num_columns, uint32_t core_id) {
  if(core_id == 0) {
    for(uint32_t i = 0; i < num_columns; i++) {
      for(uint32_t j = 0; j < num_rows; j++) {
          matrix[j * num_columns + i] = 0;
      }
    }
  }
}
