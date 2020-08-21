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

/* This library implements the discrete cosine transformation
 * The functions all follow the following format:
 *
 * TODO
 */

#define DCT_SCALING (12) // DCT constants will be scaled by 2^DCT_SCALING
#define DCT_SHIFT (16 - DCT_SCALING)

// https://web.stanford.edu/class/ee398a/handouts/lectures/07-TransformCoding.pdf#page=30
void fdct_8(int32_t const *in, int32_t *out, uint32_t stride_in, uint32_t stride_out) {
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
  out[2 * stride_out] = s5_2 * S2 >> (DCT_SCALING+DCT_SCALING);
  out[6 * stride_out] = s5_3 * S6 >> (DCT_SCALING+DCT_SCALING);
  out[5 * stride_out] = s5_4 * S5 >> (DCT_SCALING+DCT_SCALING);
  out[1 * stride_out] = s5_5 * S1 >> (DCT_SCALING+DCT_SCALING);
  out[7 * stride_out] = s5_6 * S7 >> (DCT_SCALING+DCT_SCALING);
  out[3 * stride_out] = s5_7 * S3 >> (DCT_SCALING+DCT_SCALING);
}

void fdct_8x8(int32_t const *in, int32_t *out, uint32_t stride_x, uint32_t stride_y) {
  // Create an 8x8 buffer on the stack.
  int32_t tmp[8][8];
  // Calculate all rows
  for (int i = 0; i < 8; ++i) {
    // fdct_8(&in[i*stride_y], &out[i*stride_y], stride_x, stride_x);
    fdct_8(&in[i*stride_y], &tmp[i][0], stride_x, 1);
  }
  // BARRIER
  for (int i = 0; i < 8; ++i) {
    // fdct_8(&out[i*stride_y], &out[i*stride_y], stride_y, stride_y);
    fdct_8(&tmp[0][i], &out[i], 8, stride_y);
  }
}


  /* Fast DCT algorithm due to Arai, Agui, Nakajima
   * Implementation due to Tim Kientzle
   */
  // void dct_8x8(int32_t *tga, double data[8][8], const int xpos, const int
  // ypos) {
  //   int i;
  //   int rows[8][8];

  //   static const int c1 = 1004 /* cos(pi/16) << 10 */, s1 = 200 /* sin(pi/16)
  // */,
  //                    c3 = 851 /* cos(3pi/16) << 10 */,
  //                    s3 = 569 /* sin(3pi/16) << 10 */,
  //                    r2c6 = 554 /* sqrt(2)*cos(6pi/16) << 10 */,
  //                    r2s6 = 1337 /* sqrt(2)*sin(6pi/16) << 10 */,
  //                    r2 = 181; /* sqrt(2) << 7*/

  //   int x0, x1, x2, x3, x4, x5, x6, x7, x8;

  //   /* transform rows */
  //   for (i = 0; i < 8; i++) {
  //     x0 = pixel(tga, xpos + 0, ypos + i);
  //     x1 = pixel(tga, xpos + 1, ypos + i);
  //     x2 = pixel(tga, xpos + 2, ypos + i);
  //     x3 = pixel(tga, xpos + 3, ypos + i);
  //     x4 = pixel(tga, xpos + 4, ypos + i);
  //     x5 = pixel(tga, xpos + 5, ypos + i);
  //     x6 = pixel(tga, xpos + 6, ypos + i);
  //     x7 = pixel(tga, xpos + 7, ypos + i);

  //     /* Stage 1 */
  //     x8 = x7 + x0;
  //     x0 -= x7;
  //     x7 = x1 + x6;
  //     x1 -= x6;
  //     x6 = x2 + x5;
  //     x2 -= x5;
  //     x5 = x3 + x4;
  //     x3 -= x4;

  //     /* Stage 2 */
  //     x4 = x8 + x5;
  //     x8 -= x5;
  //     x5 = x7 + x6;
  //     x7 -= x6;
  //     x6 = c1 * (x1 + x2);
  //     x2 = (-s1 - c1) * x2 + x6;
  //     x1 = (s1 - c1) * x1 + x6;
  //     x6 = c3 * (x0 + x3);
  //     x3 = (-s3 - c3) * x3 + x6;
  //     x0 = (s3 - c3) * x0 + x6;

  //     /* Stage 3 */
  //     x6 = x4 + x5;
  //     x4 -= x5;
  //     x5 = r2c6 * (x7 + x8);
  //     x7 = (-r2s6 - r2c6) * x7 + x5;
  //     x8 = (r2s6 - r2c6) * x8 + x5;
  //     x5 = x0 + x2;
  //     x0 -= x2;
  //     x2 = x3 + x1;
  //     x3 -= x1;

  //      Stage 4 and output
  //     rows[i][0] = x6;
  //     rows[i][4] = x4;
  //     rows[i][2] = x8 >> 10;
  //     rows[i][6] = x7 >> 10;
  //     rows[i][7] = (x2 - x5) >> 10;
  //     rows[i][1] = (x2 + x5) >> 10;
  //     rows[i][3] = (x3 * r2) >> 17;
  //     rows[i][5] = (x0 * r2) >> 17;
  //   }

  //   /* transform columns */
  //   for (i = 0; i < 8; i++) {
  //     x0 = rows[0][i];
  //     x1 = rows[1][i];
  //     x2 = rows[2][i];
  //     x3 = rows[3][i];
  //     x4 = rows[4][i];
  //     x5 = rows[5][i];
  //     x6 = rows[6][i];
  //     x7 = rows[7][i];

  //     /* Stage 1 */
  //     x8 = x7 + x0;
  //     x0 -= x7;
  //     x7 = x1 + x6;
  //     x1 -= x6;
  //     x6 = x2 + x5;
  //     x2 -= x5;
  //     x5 = x3 + x4;
  //     x3 -= x4;

  //     /* Stage 2 */
  //     x4 = x8 + x5;
  //     x8 -= x5;
  //     x5 = x7 + x6;
  //     x7 -= x6;
  //     x6 = c1 * (x1 + x2);
  //     x2 = (-s1 - c1) * x2 + x6;
  //     x1 = (s1 - c1) * x1 + x6;
  //     x6 = c3 * (x0 + x3);
  //     x3 = (-s3 - c3) * x3 + x6;
  //     x0 = (s3 - c3) * x0 + x6;

  //     /* Stage 3 */
  //     x6 = x4 + x5;
  //     x4 -= x5;
  //     x5 = r2c6 * (x7 + x8);
  //     x7 = (-r2s6 - r2c6) * x7 + x5;
  //     x8 = (r2s6 - r2c6) * x8 + x5;
  //     x5 = x0 + x2;
  //     x0 -= x2;
  //     x2 = x3 + x1;
  //     x3 -= x1;

  //     /* Stage 4 and output */
  //     data[0][i] = (double)((x6 + 16) >> 3);
  //     data[4][i] = (double)((x4 + 16) >> 3);
  //     data[2][i] = (double)((x8 + 16384) >> 13);
  //     data[6][i] = (double)((x7 + 16384) >> 13);
  //     data[7][i] = (double)((x2 - x5 + 16384) >> 13);
  //     data[1][i] = (double)((x2 + x5 + 16384) >> 13);
  //     data[3][i] = (double)(((x3 >> 8) * r2 + 8192) >> 12);
  //     data[5][i] = (double)(((x0 >> 8) * r2 + 8192) >> 12);
  //   }
  // }

  void dct8x8_parallel(
      int32_t const * __restrict__ in, uint32_t in_x, uint32_t in_y,
      uint32_t const volatile * __restrict__ k, uint32_t k_x, uint32_t k_y,
      int32_t volatile * __restrict__ out, uint32_t id, uint32_t numThreads) {
    int boundary_x = k_x / 2;
    int boundary_y = k_y / 2;
    // Now we only care about valid entries
    while (id < boundary_x) {
      id += numThreads;
    }
    int32_t sum;
    uint32_t weight = 0;
    for (int i = 0; i < k_x * k_y; ++i) {
      weight += k[i];
    }
    // TODO implement boundary halo
    // Start at the boundary_x
    for (int i = id; i < in_x - boundary_x; i += numThreads) {
      for (int j = boundary_y; j < in_y - boundary_y; j++) {
        sum = 0;
        for (int m = -boundary_y; m < (int)(k_y - boundary_y); m++) {
          for (int n = -boundary_x; n < (int)(k_x - boundary_x); n++) {
            sum += in[(j + m) * in_x + (i + n)] *
                   k[(m + boundary_y) * k_x + (n + boundary_x)];
          }
        }
        out[j * in_x + i] = sum / weight;
      }
    }
  }
