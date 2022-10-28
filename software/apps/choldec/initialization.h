// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#define FIXED_POINT 10
#define HALF 1023
#define FIX_DIV(a, b) ((int32_t)((a << FIXED_POINT) / b))
#define FIX_MUL(a, b) ((int32_t)((a * b + HALF) >> FIXED_POINT))
#define ABS(a) (a > 0 ? a : -a)

void transpose(int32_t *matrix, int32_t *t_matrix, int32_t n);
void matrixmult(int32_t *matrix_1, int32_t *matrix_2, int32_t *matrix_product,
                int32_t n);
void display(int32_t *matrix, uint32_t num_rows, uint32_t num_columns);
void init_matrix(int32_t *matrix, uint32_t num_rows, uint32_t num_columns,
                 int32_t a, int32_t b, int32_t c, uint32_t core_id);
void init_matrix_zeros(int32_t *matrix, uint32_t num_rows, uint32_t num_columns,
                       uint32_t core_id);

void transpose(int32_t *matrix, int32_t *t_matrix, int32_t n) {
  for (int i = 0; i < n; i++) {
    for (int j = 0; j < n; j++) {
      t_matrix[j * n + i] = matrix[i * n + j];
    }
  }
}

void matrixmult(int32_t *matrix_1, int32_t *matrix_2, int32_t *matrix_product,
                int32_t n) {
  int k;
  for (int i = 0; i < n; i++) {
    for (int j = 0; j < n; j++) { // not j < M
      matrix_product[i * n + j] = 0;
      for (k = 0; k < n; k++) {
        matrix_product[i * n + j] +=
            FIX_MUL(matrix_1[i * n + k], matrix_2[k * n + j]);
      }
    }
  }
}

void display(int32_t *matrix, uint32_t num_rows, uint32_t num_columns) {
#if defined(FOLDED)
  uint32_t i, j;
  for (i = 0; i < num_rows; i++) {
    for (j = 0; j < num_columns; j++) {
      printf("%8d", matrix[i * N_BANKS + j]);
    }
    printf("\n");
  }
#else
  uint32_t i, j;
  for (i = 0; i < num_rows; i++) {
    for (j = 0; j < num_columns; j++) {
      printf("%8d ", matrix[i * num_columns + j]);
    }
    printf("\n");
  }
#endif
}

void init_matrix(int32_t *matrix, uint32_t num_rows, uint32_t num_columns,
                 int32_t a, int32_t b, int32_t c, uint32_t core_id) {
  if (core_id == 0) {
    for (uint32_t j = 0; j < num_rows; j++) {
      for (uint32_t i = 0; i < num_columns; i++) {
        matrix[j * num_columns + i] = a * (int32_t)i + b * (int32_t)j + c;
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
