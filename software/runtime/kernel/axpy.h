// Copyright 2021 ETH Zurich and University of Bologna.
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