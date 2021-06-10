// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Samuel Riedel, ETH Zurich

/* This library implements the convolution in multiple different ways.
 * The functions all follow the following format:
 *
 * A is a vector of length A_size, B is a vector of size B_size
 */

void conv2d_parallel(int32_t const *__restrict__ in, uint32_t in_x,
                     uint32_t in_y, uint32_t const volatile *__restrict__ k,
                     uint32_t k_x, uint32_t k_y,
                     int32_t volatile *__restrict__ out, uint32_t id,
                     uint32_t numThreads) {
  int boundary_x = (int)(k_x / 2);
  int boundary_y = (int)(k_y / 2);
  // Now we only care about valid entries
  while (id < (unsigned int)boundary_x) {
    id += numThreads;
  }
  int32_t sum;
  uint32_t weight = 0;
  for (unsigned int i = 0; i < k_x * k_y; ++i) {
    weight += k[i];
  }
  // TODO implement boundary halo
  // Start at the boundary_x
  for (int i = (int)id; i < (int)in_x - boundary_x; i += (int)numThreads) {
    for (int j = boundary_y; j < (int)in_y - boundary_y; j++) {
      sum = 0;
      for (int m = -boundary_y; m < (int)k_y - boundary_y; m++) {
        for (int n = -boundary_x; n < (int)k_x - boundary_x; n++) {
          sum += in[(unsigned int)(j + m) * in_x + (unsigned int)(i + n)] *
                 (int)k[(unsigned int)(m + boundary_y) * k_x +
                        (unsigned int)(n + boundary_x)];
        }
      }
      out[(unsigned int)j * in_x + (unsigned int)i] = sum / (int)weight;
    }
  }
}

void conv2d_shifted_parallel(int32_t const *__restrict__ in, uint32_t in_x,
                             uint32_t in_y, uint32_t const *__restrict__ k,
                             uint32_t k_x, uint32_t k_y,
                             int32_t volatile *__restrict__ out, uint32_t id,
                             uint32_t numThreads) {
  int boundary_x = (int)(k_x / 2);
  int boundary_y = (int)(k_y / 2);
  int32_t sum;
  uint32_t weight = 0;
  for (unsigned int i = 0; i < k_x * k_y; ++i) {
    weight += k[i];
  }
  // TODO implement boundary halo
  // Now we only care about valid entries
  for (unsigned int i = id; i < in_x - (unsigned int)(2 * boundary_x);
       i += numThreads) {
    for (unsigned int j = 0; j < in_y - (unsigned int)(2 * boundary_y); j++) {
      sum = 0;
      for (unsigned int m = 0; m < k_y; m++) {
        for (unsigned int n = 0; n < k_x; n++) {
          sum += in[(j + m) * in_x + (i + n)] * (int)k[m * k_x + n];
        }
      }
      out[(j + (unsigned int)boundary_y) * in_x +
          (i + (unsigned int)boundary_x)] = sum / (int)weight;
    }
  }
}

void conv2d_3x3_unrolled_parallel(int32_t const *__restrict__ in, uint32_t in_x,
                                  uint32_t in_y, uint32_t const *__restrict__ k,
                                  int32_t volatile *__restrict__ out,
                                  uint32_t id, uint32_t numThreads) {
  int32_t sum;
  uint32_t weight = 0;
  for (unsigned int i = 0; i < 9; ++i) {
    weight += k[i];
  }
  // TODO implement boundary halo
  uint32_t div = in_x / numThreads;
  uint32_t rem = in_x % numThreads;
  uint32_t start = div * id;
  uint32_t end = div * (id + 1);
  // Add remainder
  start += id < rem ? id : rem;
  end += id < rem ? id : rem;
  // Now we only care about valid entries
  if (start < 1) {
    start = 1;
  }
  if (end > in_x - 1) {
    end = in_x - 1;
  }

  for (uint32_t i = start; i < end; ++i) {
    for (uint32_t j = 1; j < in_y - 1; j++) {
      sum = 0;
      sum += in[(j - 1) * in_x + (i - 1)] * (int)k[0];
      sum += in[(j - 1) * in_x + (i + 0)] * (int)k[1];
      sum += in[(j - 1) * in_x + (i + 1)] * (int)k[2];
      sum += in[(j + 0) * in_x + (i - 1)] * (int)k[3];
      sum += in[(j + 0) * in_x + (i + 0)] * (int)k[4];
      sum += in[(j + 0) * in_x + (i + 1)] * (int)k[5];
      sum += in[(j + 1) * in_x + (i - 1)] * (int)k[6];
      sum += in[(j + 1) * in_x + (i + 0)] * (int)k[7];
      sum += in[(j + 1) * in_x + (i + 1)] * (int)k[8];
      out[j * in_x + i] = sum / (int)weight;
    }
  }
}

void conv2d_3x3_shifted_unrolled_parallel(int32_t const *__restrict__ in,
                                          uint32_t in_x, uint32_t in_y,
                                          uint32_t const *__restrict__ k,
                                          int32_t volatile *__restrict__ out,
                                          uint32_t id, uint32_t numThreads) {
  int32_t sum;
  uint32_t weight = 0;
  for (int i = 0; i < 9; ++i) {
    weight += k[i];
  }
  // TODO implement boundary halo
  // Now we only care about valid entries
  for (unsigned int i = id; i < in_x - 2; i += numThreads) {
    for (unsigned int j = 0; j < in_y - 2; j++) {
      sum = 0;
      sum += in[(j + 0) * in_x + (i + 0)] * (int)k[0];
      sum += in[(j + 0) * in_x + (i + 1)] * (int)k[1];
      sum += in[(j + 0) * in_x + (i + 2)] * (int)k[2];
      sum += in[(j + 1) * in_x + (i + 0)] * (int)k[3];
      sum += in[(j + 1) * in_x + (i + 1)] * (int)k[4];
      sum += in[(j + 1) * in_x + (i + 2)] * (int)k[5];
      sum += in[(j + 2) * in_x + (i + 0)] * (int)k[6];
      sum += in[(j + 2) * in_x + (i + 1)] * (int)k[7];
      sum += in[(j + 2) * in_x + (i + 2)] * (int)k[8];
      out[(j + 1) * in_x + (i + 1)] = sum / (int)weight;
    }
  }
}

// Testing
// Initialize the image in parallel
void init_conv2d_image(volatile int32_t *img, uint32_t img_x, uint32_t img_y,
                       uint32_t id, uint32_t numThreads) {
  // Parallelize over rows
  if (img_y > img_x) {
    for (int i = (int)id; i < (int)img_y; i += (int)numThreads) {
      for (int j = 0; j < (int)img_x; ++j) {
        img[(unsigned int)i * img_x + (unsigned int)j] = (i % 16) + (j % 4);
      }
    }
  } else {
    for (int j = (int)id; j < (int)img_x; j += (int)numThreads) {
      for (int i = 0; i < (int)img_y; ++i) {
        img[(unsigned int)i * img_x + (unsigned int)j] = (i % 16) + (j % 4);
      }
    }
  }
}

// Initialize the image in parallel
void zero_conv2d_image(volatile int32_t *img, uint32_t img_x, uint32_t img_y,
                       uint32_t id, uint32_t numThreads) {
  // Parallelize over rows
  if (img_y > img_x) {
    for (int i = (int)id; i < (int)img_y; i += (int)numThreads) {
      for (int j = 0; j < (int)img_x; ++j) {
        img[(unsigned int)i * img_x + (unsigned int)j] = 0;
      }
    }
  } else {
    for (int j = (int)id; j < (int)img_x; j += (int)numThreads) {
      for (int i = 0; i < (int)img_y; ++i) {
        img[(unsigned int)i * img_x + (unsigned int)j] = 0;
      }
    }
  }
}

extern uint32_t barrier_init;

// Verify and reset the image in parallel
int verify_conv2d_image(volatile int32_t *img, uint32_t img_x, uint32_t img_y,
                        uint32_t id, uint32_t numThreads) {
  // Parallelize over rows
  for (int i = (int)id + 1; i < (int)img_y - 1; i += (int)numThreads) {
    int y = i % 16;
    if (i % 16 == 0)
      y = 4;
    if (i % 16 == 15)
      y = 11;
    for (int j = 1; j < (int)img_x - 1; ++j) {
      int x = ((j % 4) / 2) + 1;
      if ((int)img[i * (int)img_x + j] != x + y) {
        return (i + j) == 0 ? -1 : i * (int)img_x + j;
      }
      img[i * (int)img_x + j] = 0;
    }
  }
  return 0;
}
