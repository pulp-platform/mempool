// Copyright 2020 ETH Zurich and University of Bologna.
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

// Author: Samuel Riedel, ETH Zurich

/* This library implements the convolution in multiple different ways.
 * The functions all follow the following format:
 *
 * A is a vector of length A_size, B is a vector of size B_size
 */

// #pragma once

void conv2d_parallel(int32_t const *__restrict__ in, uint32_t in_x,
                     uint32_t in_y, uint32_t const volatile *__restrict__ k,
                     uint32_t k_x, uint32_t k_y,
                     int32_t volatile *__restrict__ out, uint32_t id,
                     uint32_t numThreads) {
  uint32_t boundary_x = k_x / 2;
  uint32_t boundary_y = k_y / 2;
  int32_t sum;
  uint32_t weight;
  for (int i = 0; i < k_x * k_y; ++i) {
    weight += k[i];
  }
  // TODO implement boundary halo
  // Now we only care about valid entries
  // Start at the boundary_x
  if (id < boundary_x)
    return;
  for (int i = id; i < in_x - boundary_x; i += numThreads) {
    for (int j = boundary_y; j < in_y - boundary_y; j++) {
      sum = 0;
      for (int m = -boundary_y; m < k_y - boundary_y; m++) {
        for (int n = -boundary_x; n < k_x - boundary_x; n++) {
          sum += in[(j + m) * in_x + (i + n)] *
                 k[(m + boundary_y) * k_x + (n + boundary_x)];
        }
      }
      out[j * in_x + i] = sum / weight;
    }
  }
}

void conv2d_shifted_parallel(int32_t const *__restrict__ in, uint32_t in_x,
                             uint32_t in_y, uint32_t const *__restrict__ k,
                             uint32_t k_x, uint32_t k_y,
                             int32_t volatile *__restrict__ out, uint32_t id,
                             uint32_t numThreads) {
  uint32_t boundary_x = k_x / 2;
  uint32_t boundary_y = k_y / 2;
  int32_t sum;
  uint32_t weight;
  for (int i = 0; i < k_x * k_y; ++i) {
    weight += k[i];
  }
  // TODO implement boundary halo
  // Now we only care about valid entries
  for (int i = id; i < in_x - (2 * boundary_x); i += numThreads) {
    for (int j = 0; j < in_y - (2 * boundary_y); j++) {
      sum = 0;
      for (int m = 0; m < k_y; m++) {
        for (int n = 0; n < k_x; n++) {
          sum += in[(j + m) * in_x + (i + n)] * k[m * k_x + n];
        }
      }
      out[(j + boundary_y) * in_x + (i + boundary_x)] = sum / weight;
    }
  }
}

void conv2d_3x3_unrolled_parallel(int32_t const *__restrict__ in, uint32_t in_x,
                                  uint32_t in_y, uint32_t const *__restrict__ k,
                                  int32_t volatile *__restrict__ out,
                                  uint32_t id, uint32_t numThreads) {
  uint32_t boundary_x = 1;
  uint32_t boundary_y = 1;
  int32_t sum;
  uint32_t weight;
  for (int i = 0; i < 9; ++i) {
    weight += k[i];
  }
  // TODO implement boundary halo
  // Now we only care about valid entries
  if (id < 1)
    return;

  for (int i = id; i < in_x - 1; i += numThreads) {
    for (int j = 1; j < in_y - 1; j++) {
      sum = 0;
      sum += in[(j - 1) * in_x + (i - 1)] * k[0];
      sum += in[(j - 1) * in_x + (i + 0)] * k[1];
      sum += in[(j - 1) * in_x + (i + 1)] * k[2];
      sum += in[(j + 0) * in_x + (i - 1)] * k[3];
      sum += in[(j + 0) * in_x + (i + 0)] * k[4];
      sum += in[(j + 0) * in_x + (i + 1)] * k[5];
      sum += in[(j + 1) * in_x + (i - 1)] * k[6];
      sum += in[(j + 1) * in_x + (i + 0)] * k[7];
      sum += in[(j + 1) * in_x + (i + 1)] * k[8];
      out[j * in_x + i] = sum / weight;
    }
  }
}

void conv2d_3x3_shifted_unrolled_parallel(int32_t const *__restrict__ in,
                                          uint32_t in_x, uint32_t in_y,
                                          uint32_t const *__restrict__ k,
                                          int32_t volatile *__restrict__ out,
                                          uint32_t id, uint32_t numThreads) {
  uint32_t boundary_x = 1;
  uint32_t boundary_y = 1;
  int32_t sum;
  uint32_t weight;
  for (int i = 0; i < 9; ++i) {
    weight += k[i];
  }
  // TODO implement boundary halo
  // Now we only care about valid entries
  for (int i = id; i < in_x - 2; i += numThreads) {
    for (int j = 0; j < in_y - 2; j++) {
      sum = 0;
      sum += in[(j + 0) * in_x + (i + 0)] * k[0];
      sum += in[(j + 0) * in_x + (i + 1)] * k[1];
      sum += in[(j + 0) * in_x + (i + 2)] * k[2];
      sum += in[(j + 1) * in_x + (i + 0)] * k[3];
      sum += in[(j + 1) * in_x + (i + 1)] * k[4];
      sum += in[(j + 1) * in_x + (i + 2)] * k[5];
      sum += in[(j + 2) * in_x + (i + 0)] * k[6];
      sum += in[(j + 2) * in_x + (i + 1)] * k[7];
      sum += in[(j + 2) * in_x + (i + 2)] * k[8];
      out[(j + 1) + in_x + (i + 1)] = sum / weight;
    }
  }
}

void conv2d_3x3_shifted_unrolled(int32_t const *__restrict__ in, uint32_t in_x,
                                 uint32_t in_y, uint32_t const *__restrict__ k,
                                 int32_t volatile *__restrict__ out) {
  uint32_t boundary_x = 1;
  uint32_t boundary_y = 1;
  int32_t sum;
  uint32_t weight;
  for (int i = 0; i < 9; ++i) {
    weight += k[i];
  }
  // TODO implement boundary halo
  // Now we only care about valid entries
  for (int i = 0; i < in_x - 2; i += 1) {
    for (int j = 0; j < in_y - 2; j++) {
      sum = 0;
      sum += in[(j + 0) * in_x + (i + 0)] * k[0];
      sum += in[(j + 0) * in_x + (i + 1)] * k[1];
      sum += in[(j + 0) * in_x + (i + 2)] * k[2];
      sum += in[(j + 1) * in_x + (i + 0)] * k[3];
      sum += in[(j + 1) * in_x + (i + 1)] * k[4];
      sum += in[(j + 1) * in_x + (i + 2)] * k[5];
      sum += in[(j + 2) * in_x + (i + 0)] * k[6];
      sum += in[(j + 2) * in_x + (i + 1)] * k[7];
      sum += in[(j + 2) * in_x + (i + 2)] * k[8];
      out[(j + 1) + in_x + (i + 1)] = sum / weight;
    }
  }
}

// void convolution(uint32_t id, uint32_t numThreads) { uint32_t sum; }
