// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Yichao Zhang, ETH Zurich

int32_t AXPY(uint32_t n, int32_t da, int32_t *x, int32_t *y) {
  uint32_t i = 0;
  if (da == 0)
    return (0);

  while (i < n) {
    y[i] += da * x[i];
    i++;
  }
  return (0);
}

int32_t AXPY_unloop(uint32_t n, int32_t da, int32_t *x, int32_t *y) {
  uint32_t i = 0;
  uint32_t j = 0;
  if (da == 0)
    return (0);

  uint32_t partial = n % 4;

  while (i < n - partial) {
    int32_t x0 = x[0];
    int32_t x1 = x[1];
    int32_t x2 = x[2];
    int32_t x3 = x[3];
    int32_t acc = y[0];
    int32_t acc1 = y[1];
    int32_t acc2 = y[2];
    int32_t acc3 = y[3];

    acc += da * x0;
    acc1 += da * x1;
    acc2 += da * x2;
    acc3 += da * x3;

    y[0] = acc;
    y[1] = acc1;
    y[2] = acc2;
    y[3] = acc3;

    x += 4;
    y += 4;
    i += 4;
  }

  while (j < partial) {
    y[0] += da * x[0];
    x += 1;
    y += 1;
    j++;
  }
  return (0);
}

int32_t AXPY_unloop_x4(int32_t da, int32_t *x, int32_t *y) {
  int32_t x0 = x[0];
  int32_t x1 = x[1];
  int32_t x2 = x[2];
  int32_t x3 = x[3];
  int32_t acc = y[0];
  int32_t acc1 = y[1];
  int32_t acc2 = y[2];
  int32_t acc3 = y[3];

  acc += da * x0;
  acc1 += da * x1;
  acc2 += da * x2;
  acc3 += da * x3;

  y[0] = acc;
  y[1] = acc1;
  y[2] = acc2;
  y[3] = acc3;
  return (0);
}

// Function start
// Serial calculation by core 0
void calc_axpy_serial(int32_t *matrix_X, int32_t *matrix_Y, int32_t alpha,
                      uint32_t elements, uint32_t core_id) {
  if (core_id == 0) {
    AXPY(elements, alpha, &matrix_X[0], &matrix_Y[0]);
  }
}

// Serial calculation with 4 time unloop by core 0
void calc_axpy_serial_unloop(int32_t *matrix_X, int32_t *matrix_Y,
                             int32_t alpha, uint32_t elements,
                             uint32_t core_id) {
  if (core_id == 0) {
    AXPY_unloop(elements, alpha, &matrix_X[0], &matrix_Y[0]);
  }
}

// Parallel calculation
void calc_axpy(int32_t *matrix_X, int32_t *matrix_Y, int32_t alpha,
               uint32_t elements, uint32_t core_id, uint32_t num_cores) {
  // Support the elements number is not the devided by the core numbers;
  // The corresponding core ID will take the partial elements.
  uint32_t split = elements / num_cores;
  uint32_t partial = elements % num_cores;
  if (core_id < partial) {
    uint32_t const c_start = core_id * (split + 1);
    uint32_t const j = split + 1;
    AXPY(j, alpha, &matrix_X[c_start], &matrix_Y[c_start]);
  } else {
    uint32_t const c_start = core_id * split + partial;
    AXPY(split, alpha, &matrix_X[c_start], &matrix_Y[c_start]);
  }
}

// Parallel calculation with 4 times unloop
void calc_axpy_unloop(int32_t *matrix_X, int32_t *matrix_Y, int32_t alpha,
                      uint32_t elements, uint32_t core_id, uint32_t num_cores) {
  // Support the elements number is not the devided by the core numbers;
  // The corresponding core ID will take the partial elements.
  uint32_t split = elements / num_cores;
  uint32_t partial = elements % num_cores;
  if (core_id < partial) {
    uint32_t const c_start = core_id * (split + 1);
    uint32_t const j = split + 1;
    AXPY_unloop(j, alpha, &matrix_X[c_start], &matrix_Y[c_start]);
  } else {
    uint32_t const c_start = core_id * split + partial;
    AXPY_unloop(split, alpha, &matrix_X[c_start], &matrix_Y[c_start]);
  }
}

// Parallel calculation with 4 times unloop align with banks
void calc_axpy_unloop_x4_localbank(int32_t *matrix_X, int32_t *matrix_Y,
                                   int32_t alpha, uint32_t elements,
                                   uint32_t core_id, uint32_t num_cores) {
  uint32_t const bank_num = num_cores * 4;
  // Do the calculation that redundant elements cannot be unloop;
  // Use core0 is less overhead than found the local
  uint32_t partial = elements % 4;
  if (core_id == 0) {
    if (partial != 0) {
      uint32_t c_start = elements - partial + 1;
      AXPY(partial, alpha, &matrix_X[c_start], &matrix_Y[c_start]);
    }
  }
  // Do unloop 4 times
  uint32_t const total_unloop = elements - partial;
  uint32_t const c_start = core_id * 4;
  for (uint32_t c = c_start; c <= total_unloop - 4; c += bank_num) {
    AXPY_unloop_x4(alpha, &matrix_X[c], &matrix_Y[c]);
  }
}
