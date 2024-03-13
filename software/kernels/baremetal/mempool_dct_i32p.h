// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Samuel Riedel, ETH Zurich

/* This library implements the discrete cosine transformation
 * The functions all follow the following format:
 *
 * TODO
 */

#define DCT_SCALING (8) // DCT constants will be scaled by 2^DCT_SCALING
#define DCT_SHIFT (16 - DCT_SCALING)

// https://web.stanford.edu/class/ee398a/handouts/lectures/07-TransformCoding.pdf#page=30
void fdct_8(int32_t const *in, int32_t *out, uint32_t stride_in,
            uint32_t stride_out) {
  // Constants: ck = cos(pi*k/16) * 10^16 >> DCT_SHIFT
  static const int32_t c0 = 65536 >> (DCT_SHIFT); // 1
  static const int32_t c2 = 60547 >> (DCT_SHIFT); // sqrt(2+sqrt(2))/2
  static const int32_t c4 = 46341 >> (DCT_SHIFT); // 1/sqrt(2)
  static const int32_t c6 = 25080 >> (DCT_SHIFT); // sqrt(2-sqrt(2))/2
  // Constants: Scaling factor: Sk = 1/(4*ck)  * 10^16 >> DCT_SHIFT
  static const int32_t S0 = 23170 >> (DCT_SHIFT); // 1/(2*sqrt(2))
  static const int32_t S1 = 16705 >> (DCT_SHIFT); // 1/(4*c1)
  static const int32_t S2 = 17734 >> (DCT_SHIFT); // 1/(4*c2)
  static const int32_t S3 = 19705 >> (DCT_SHIFT); // 1/(4*c3)
  static const int32_t S4 = 23171 >> (DCT_SHIFT); // 1/(4*c4)
  static const int32_t S5 = 29490 >> (DCT_SHIFT); // 1/(4*c5)
  static const int32_t S6 = 42814 >> (DCT_SHIFT); // 1/(4*c6)
  static const int32_t S7 = 83982 >> (DCT_SHIFT); // 1/(4*c7)

  // Read input
  int32_t x0 = in[0 * stride_in];
  int32_t x1 = in[1 * stride_in];
  int32_t x2 = in[2 * stride_in];
  int32_t x3 = in[3 * stride_in];
  int32_t x4 = in[4 * stride_in];
  int32_t x5 = in[5 * stride_in];
  int32_t x6 = in[6 * stride_in];
  int32_t x7 = in[7 * stride_in];

  // Stage 1
  int32_t s1_0 = x0 + x7;
  int32_t s1_1 = x1 + x6;
  int32_t s1_2 = x2 + x5;
  int32_t s1_3 = x3 + x4;
  int32_t s1_4 = x3 - x4;
  int32_t s1_5 = x2 - x5;
  int32_t s1_6 = x1 - x6;
  int32_t s1_7 = x0 - x7;

  // Stage 2
  int32_t s2_0 = s1_0 + s1_3;
  int32_t s2_1 = s1_1 + s1_2;
  int32_t s2_2 = s1_1 - s1_2;
  int32_t s2_3 = s1_0 - s1_3;
  int32_t s2_4 = -s1_4 - s1_5;
  int32_t s2_5 = s1_5 + s1_6;
  int32_t s2_6 = s1_6 + s1_7;
  int32_t s2_7 = s1_7;

  // Stage 3
  int32_t s3_0 = s2_0 + s2_1;
  int32_t s3_1 = s2_0 - s2_1;
  int32_t s3_2 = (s2_2 + s2_3) * c4;
  int32_t s3_3 = s2_3 * c0;
  int32_t s3_4 = s2_4 * (c2 - c6);
  int32_t s3_5 = s2_5 * c4;
  int32_t s3_6 = s2_6 * (c2 + c6);
  int32_t s3_7 = s2_7 * c0;
  int32_t s3_8 = (s2_4 + s2_6) * c6;

  // Stage 4
  int32_t s4_0 = s3_0;
  int32_t s4_1 = s3_1;
  int32_t s4_2 = s3_2 + s3_3;
  int32_t s4_3 = s3_3 - s3_2;
  int32_t s4_4 = -s3_4 - s3_8;
  int32_t s4_5 = s3_5 + s3_7;
  int32_t s4_6 = s3_6 - s3_8;
  int32_t s4_7 = s3_7 - s3_5;

  // Stage 5
  int32_t s5_0 = s4_0;
  int32_t s5_1 = s4_1;
  int32_t s5_2 = s4_2;
  int32_t s5_3 = s4_3;
  int32_t s5_4 = s4_4 + s4_7;
  int32_t s5_5 = s4_5 + s4_6;
  int32_t s5_6 = s4_5 - s4_6;
  int32_t s5_7 = s4_7 - s4_4;

  // Scaling and bitreverse
  out[0 * stride_out] = s5_0 * S0 >> (DCT_SCALING);
  out[4 * stride_out] = s5_1 * S4 >> (DCT_SCALING);
  out[2 * stride_out] = s5_2 * S2 >> (DCT_SCALING + DCT_SCALING);
  out[6 * stride_out] = s5_3 * S6 >> (DCT_SCALING + DCT_SCALING);
  out[5 * stride_out] = s5_4 * S5 >> (DCT_SCALING + DCT_SCALING);
  out[1 * stride_out] = s5_5 * S1 >> (DCT_SCALING + DCT_SCALING);
  out[7 * stride_out] = s5_6 * S7 >> (DCT_SCALING + DCT_SCALING);
  out[3 * stride_out] = s5_7 * S3 >> (DCT_SCALING + DCT_SCALING);
}

void fdct_8x8(int32_t const *in, int32_t *out, uint32_t stride_x,
              uint32_t stride_y) {
  // Create an 8x8 buffer on the stack.
  int32_t tmp[8][8];
  // Calculate all rows
  for (uint32_t i = 0; i < 8; ++i) {
    // fdct_8(&in[i*stride_y], &out[i*stride_y], stride_x, stride_x);
    fdct_8(&in[i * stride_y], &tmp[i][0], stride_x, 1);
  }
  // BARRIER
  for (uint32_t i = 0; i < 8; ++i) {
    // fdct_8(&out[i*stride_y], &out[i*stride_y], stride_y, stride_y);
    fdct_8(&tmp[0][i], &out[i * stride_x], 8, stride_y);
  }
}

void fdct_8x8_parallel(int32_t const *in, uint32_t in_x, uint32_t in_y,
                       int32_t *__restrict__ out, uint32_t id,
                       uint32_t numThreads) {
  // Assume image is divisible into 8x8 chunks
  uint32_t tiles_x = in_x >> 3;
  uint32_t tiles_y = in_y >> 3;
  uint32_t tile_id;
  if (tiles_x == (numThreads / 2)) {
    // Process two rows of tiles at once to use local memory
    tile_id = id / 2;
    if (id & 0x1) {
      tile_id += tiles_x; // Process second row
    }
  } else {
    tile_id = id;
  }
  for (uint32_t i = tile_id; i < tiles_x * tiles_y; i += numThreads) {
    uint32_t tile_x = i % tiles_x;
    uint32_t tile_y = i / tiles_x;
    fdct_8x8(&in[(8 * tile_x) + (8 * in_x * tile_y)],
             &out[(8 * tile_x) + (8 * in_x * tile_y)], 1, in_x);
  }
}
