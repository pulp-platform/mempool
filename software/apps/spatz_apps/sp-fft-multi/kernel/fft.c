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

// Author: Diyou Shen, Matteo Perotti, ETH Zurich

#include "fft.h"

/* Phase 1 of vector FFT on muti-core */
/* This function would be run several times in main with barrier*/

void fft_p1 (float *src, float *buf, const float *twi,
             const uint32_t nfft,  const uint32_t ntwi,
             const uint32_t cid,   const uint32_t num_cores,
             const uint32_t stage, const uint32_t len) {

  size_t avl = (size_t) len;
  size_t vl;

  const float *re_twi, *im_twi;
  const float *re_u_i, *im_u_i, *re_l_i, *im_l_i;
  float *re_u_o, *im_u_o, *re_l_o, *im_l_o;

  const float *i_buf;
  float *o_buf;
  i_buf = src;
  o_buf = buf;

  // Is there a more efficient way to calculate these pointers?
  for (uint32_t group = 0; group < (1 << stage); group ++) {
    // divide cores into 2^(stage) groups
    if (cid < ((num_cores >> stage)*(group+1))) {
      // stage 0: 1 group, 0;
      // stage 1: 2 group, 0 : nfft/2;
      // stage 2: 4 group, 0 : nfft/4 : 2*nfft/4 : 3*nfft/4;
      // ......

      // offset for different groups
      uint32_t offset = (nfft >> stage) * group;
      uint32_t idx    = cid - (num_cores >> stage) * group;

      // inputs pointer
      re_u_i = i_buf  + offset + idx * len;
      re_l_i = re_u_i + (nfft >> (stage + 1));
      im_u_i = re_u_i + nfft;
      im_l_i = re_l_i + nfft;

      // output pointer
      re_u_o = o_buf  + offset + idx * len;
      re_l_o = re_u_o + (nfft >> (stage + 1));
      im_u_o = re_u_o + nfft;
      im_l_o = re_l_o + nfft;

      // twiddle pointer
      // twiddle will not need add group offset
      // main will jump to next twiddle
      // each group will have the same twiddle
      re_twi = twi    + idx * len;
      im_twi = re_twi + ntwi;

      // Once the core gets the pointer, it needs to leave the loop
      break;
    }
  }

  // initial value of avl has been calculated earlier
  for (; avl > 0; avl -= vl) {
    // re_u_o = re_u_i + re_l_i;
    // im_u_o = im_u_i + im_l_i;
    // re_l_o = (re_u_i - re_l_i) * re_twi - (im_u_i - im_l_i) * im_twi;
    // im_l_o = (re_u_i - re_l_i) * im_twi + (im_u_i - im_l_i) * re_twi;
    asm volatile("vsetvli %0, %1, e32, m4, ta, ma" : "=r"(vl) : "r"(avl));

    asm volatile("vle32.v v0, (%0);" ::"r"(re_u_i)); // v0: Re upper wing
    re_u_i += vl;
    asm volatile("vle32.v v4, (%0);" ::"r"(re_l_i)); // v4: Re lower wing
    re_l_i += vl;
    asm volatile("vfadd.vv v16, v0, v4"); // v16: Re butterfly output upper wing
    asm volatile("vfsub.vv v0, v0, v4");  // v0: Re butterfly output upper wing

    asm volatile("vle32.v v8, (%0);" ::"r"(im_u_i)); // v8: Im upper wing
    im_u_i += vl;
    asm volatile("vle32.v v12, (%0);" ::"r"(im_l_i)); // v12: Im lower wing
    im_l_i += vl;

    asm volatile("vfadd.vv v20, v8, v12"); // v20: Im butterfly output upper wing

    asm volatile("vfsub.vv v4, v8, v12"); // v4: Im butterfly output upper wing

    // Load the twiddle vector
    asm volatile("vle32.v v8, (%0);" ::"r"(re_twi)); // v8: Re twi
    re_twi += vl;
    asm volatile("vle32.v v12, (%0);" ::"r"(im_twi)); // v12: Im twi
    im_twi += vl;

    // Twiddle the lower wing
    // re_l_o = - v0 * v8  - v4 * v12
    // im_l_o =   v0 * v12 + v4 * v8
    // Store 1:1 the output result
    // Sequence do not need to shuffle in first phase
    asm volatile("vfmul.vv v24, v0, v8");
    asm volatile("vfnmsac.vv v24, v4, v12"); // v24: Re butterfly output
                                             // twiddled lower wing
    asm volatile("vse32.v v16, (%0)" ::"r"(re_u_o));
    re_u_o += vl;
    asm volatile("vse32.v v20, (%0)" ::"r"(im_u_o));
    im_u_o += vl;
    asm volatile("vfmul.vv v28, v0, v12");
    asm volatile("vfmacc.vv v28, v4, v8"); // v28: Im butterfly output
                                           // twiddled lower wing

    asm volatile("vse32.v v24, (%0)" ::"r"(re_l_o));
    re_l_o += vl;
    asm volatile("vse32.v v28, (%0)" ::"r"(im_l_o));
    im_l_o += vl;
  }
}

/* Phase 2 of vector FFT on muti-core */
// DIF Cooley-Tukey algorithm
// At every iteration, we store indexed
void fft_p2(float *s, float *buf, const float *twi, float *out,
            const uint16_t *seq_idx, const uint32_t nfft,
            const uint32_t nfft_ori, const uint32_t log2_nfft,
            const uint32_t stride,   const uint32_t stride_e, const uint32_t ntwi) {

  // Always run in dual-core mode

  // Real part of the twiddles
  const float *re_twi = twi;
  // Img part of the twiddles
  const float *im_twi = twi + ntwi;

  // Keep half of the samples in a vector register
  size_t avl;
  size_t vl;

  // Loop through the butterfly stages
  for (uint32_t bf = 0; bf < log2_nfft; ++bf) {
    // Keep half of the samples in a vector register
    avl = nfft >> 1;
    // Swap between the two buffers
    const float *i_buf;
    float *o_buf;
    i_buf = !(bf & 1) ? buf : s;
    o_buf = !(bf & 1) ? s : buf;

    // Last iteration
    if (bf == log2_nfft - 1)
      o_buf = buf;

    // Update pointers
    const float *re_u_i = i_buf;
    const float *im_u_i = i_buf + nfft_ori;
    const float *re_l_i = re_u_i + (nfft >> 1);
    const float *im_l_i = im_u_i + (nfft >> 1);
    float *re_u_o = o_buf;
    float *im_u_o = o_buf + nfft_ori;
    float *re_l_o = re_u_o + (nfft >> 1);
    float *im_l_o = im_u_o + (nfft >> 1);

    float *re_u_s = out;
    float *im_u_s = out + nfft_ori;
    float *re_l_s = re_u_s + (nfft_ori >> 1);
    float *im_l_s = im_u_s + (nfft_ori >> 1);

    // Stripmine the whole vector for this butterfly stage
    for (; avl > 0; avl -= vl) {
      // re_u_o = re_u_i + re_l_i;
      // im_u_o = im_u_i + im_l_i;
      // re_l_o = (re_u_i - re_l_i) * re_twi - (im_u_i - im_l_i) * im_twi;
      // im_l_o = (re_u_i - re_l_i) * im_twi + (im_u_i - im_l_i) * re_twi;
      // Stripmine
      // Group 4 registers as a larger register to improve performance
      asm volatile("vsetvli %0, %1, e32, m4, ta, ma" : "=r"(vl) : "r"(avl));

      // 2 load/store with 2 calc sometimes gives a better performance (window of 4 insn)
      asm volatile("vle32.v v0, (%0);" ::"r"(re_u_i)); // v0: Re upper wing
      re_u_i += vl;
      asm volatile("vle32.v v4, (%0);" ::"r"(re_l_i)); // v4: Re lower wing
      re_l_i += vl;

      asm volatile("vfadd.vv v16, v0, v4"); // v16: Re butterfly output upper wing
      asm volatile("vfsub.vv v0, v0, v4");  // v0: Re butterfly output upper wing

      asm volatile("vle32.v v8, (%0);" ::"r"(im_u_i)); // v8: Im upper wing
      im_u_i += vl;
      asm volatile("vle32.v v12, (%0);" ::"r"(im_l_i)); // v12: Im lower wing
      im_l_i += vl;

      asm volatile("vfadd.vv v20, v8, v12"); // v20: Im butterfly output upper wing
      asm volatile("vfsub.vv v4, v8, v12"); // v4: Im butterfly output upper wing

      // Load the index vector. If last step, do strided store
      // Otherwise, it's the helper index for the permutations (this is a mask
      // vector)
      if (bf == log2_nfft - 1) {
        // Last store is a strided pattern
        // use strided store instead of index store to improve performance
        asm volatile("vsse32.v v16, (%0), %1" ::"r"(re_u_s),"r"(stride));
        asm volatile("vsse32.v v20, (%0), %1" ::"r"(im_u_s),"r"(stride));
        asm volatile("vsse32.v v0,  (%0), %1" ::"r"(re_l_s),"r"(stride));
        asm volatile("vsse32.v v4,  (%0), %1" ::"r"(im_l_s),"r"(stride));
        // update the store pointer
        re_u_s += (vl << stride_e);
        im_u_s += (vl << stride_e);
        re_l_s += (vl << stride_e);
        im_l_s += (vl << stride_e);
      } else {
        // TODO: Actually, there is no need to st then ld
        // Can we add an insn to shuffle the elem position?
        // Load the twiddle vector
        asm volatile("vle32.v v8, (%0);" ::"r"(re_twi)); // v8: Re twi
        re_twi += vl;
        asm volatile("vle32.v v12, (%0);" ::"r"(im_twi)); // v12: Im twi
        im_twi += vl;

        // Twiddle the lower wing
        // re_l_o = - v0 * v8  - v4 * v12
        // im_l_o =   v0 * v12 + v4 * v8
        asm volatile("vfmul.vv v24, v0, v8");
        asm volatile("vfnmsac.vv v24, v4, v12"); // v24: Re butterfly output
                                                 // twiddled lower wing
        asm volatile("vfmul.vv v28, v0, v12");
        asm volatile("vfmacc.vv v28, v4, v8"); // v28: Im butterfly output
                                               // twiddled lower wing
        // Load the sequential indices dirctly
        asm volatile("vle16.v v12, (%0)" ::"r"(seq_idx)); // v24: index vector
        seq_idx += vl;
        re_u_o = o_buf;
        im_u_o = o_buf + nfft_ori;
        re_l_o = re_u_o + (nfft >> 2);
        im_l_o = im_u_o + (nfft >> 2);

        asm volatile("vsuxei16.v v16, (%0), v12" ::"r"(re_u_o));
        asm volatile("vsuxei16.v v20, (%0), v12" ::"r"(im_u_o));
        asm volatile("vsuxei16.v v24, (%0), v12" ::"r"(re_l_o));
        asm volatile("vsuxei16.v v28, (%0), v12" ::"r"(im_l_o));
      }
    }
  }
}
