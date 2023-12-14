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

// Author: Domenic Wüthrich, ETH Zurich

#include "sp-imatmul.h"

#define MIN(a, b) ((a) < (b) ? (a) : (b))

void matmul(int32_t *c, const int32_t *a, const int32_t *b,
            const unsigned int M, const unsigned int N, const unsigned int P) {
  if (M <= 4) {
    matmul_2xVL(c, a, b, 0, M, N, P, 0, P);
  } else if (M <= 8) {
    matmul_4xVL(c, a, b, 0, M, N, P, 0, P);
  } else {
    matmul_8xVL(c, a, b, 0, M, N, P, 0, P);
  }
}

// ---------------
// 2xVL
// ---------------

void matmul_2xVL(int32_t *c, const int32_t *a, const int32_t *b,
                 const unsigned int m_start, const unsigned int m_end,
                 const unsigned int N, const unsigned int P,
                 const unsigned int p_start, const unsigned int p_end) {

  unsigned int p = p_start;
  while (p < p_end) {
    // Calculate the vl
    size_t gvl;
    asm volatile("vsetvli %[gvl], %[vl], e32, m8, ta, ma"
                 : [gvl] "=r"(gvl)
                 : [vl] "r"(p_end - p));

    const int32_t *b_ = b + p;
    int32_t *c_ = c + p;

    for (unsigned int m = m_start; m < m_end; m += 2) {
      const int32_t *a_ = a + m * N;
      const int32_t *a__ = a_;

      asm volatile("vle32.v v16, (%0);" ::"r"(b_));
      const int32_t *b__ = b_ + P;

      int32_t *c__ = c_ + m * P;

      int32_t t0, t1;

      t0 = *a__;
      a__ += N;
      t1 = *a__;

      unsigned int n = 0;

      while (n < N) {
        a__ = a_ + ++n;

        asm volatile("vle32.v v24, (%0);" ::"r"(b__));
        b__ += P;

        if (n == 1) {
          asm volatile("vmul.vx v0, v16, %0" ::"r"(t0));
          t0 = *a__;
          a__ += N;
          asm volatile("vmul.vx v8, v16, %0" ::"r"(t1));
          t1 = *a__;
        } else {
          asm volatile("vmacc.vx v0, %0, v16" ::"r"(t0));
          t0 = *a__;
          a__ += N;
          asm volatile("vmacc.vx v8, %0, v16" ::"r"(t1));
          t1 = *a__;
        }

        a__ = a_ + ++n;

        if (n == N)
          break;

        asm volatile("vle32.v v16, (%0);" ::"r"(b__));
        b__ += P;

        asm volatile("vmacc.vx v0, %0, v24" ::"r"(t0));
        t0 = *a__;
        a__ += N;
        asm volatile("vmacc.vx v8, %0, v24" ::"r"(t1));
        t1 = *a__;
      }

      asm volatile("vmacc.vx v0, %0, v24" ::"r"(t0));
      asm volatile("vse32.v v0, (%0);" ::"r"(c__));
      c__ += P;
      asm volatile("vmacc.vx v8, %0, v24" ::"r"(t1));
      asm volatile("vse32.v v8, (%0);" ::"r"(c__));
    }

    p += gvl;
  }
}

// ---------------
// 4xVL
// ---------------

void matmul_4xVL(int32_t *c, const int32_t *a, const int32_t *b,
                 const unsigned int m_start, const unsigned int m_end,
                 const unsigned int N, const unsigned int P,
                 const unsigned int p_start, const unsigned int p_end) {

  unsigned int p = p_start;
  while (p < p_end) {
    // Calculate the vl
    size_t gvl;
    asm volatile("vsetvli %[gvl], %[vl], e32, m4, ta, ma"
                 : [gvl] "=r"(gvl)
                 : [vl] "r"(p_end - p));

    const int32_t *b_ = b + p;
    int32_t *c_ = c + p;

    for (unsigned int m = m_start; m < m_end; m += 4) {
      const int32_t *a_ = a + m * N;
      const int32_t *a__ = a_;

      asm volatile("vle32.v v16, (%0);" ::"r"(b_));
      const int32_t *b__ = b_ + P;

      int32_t *c__ = c_ + m * P;

      int32_t t0, t1, t2, t3;

      t0 = *a__;
      a__ += N;
      t1 = *a__;
      a__ += N;
      t2 = *a__;
      a__ += N;
      t3 = *a__;

      unsigned int n = 0;

      while (n < N) {
        asm volatile("vle32.v v20, (%0);" ::"r"(b__));
        b__ += P;

        a__ = a_ + ++n;

        if (n == 1) {
          asm volatile("vmul.vx v0, v16, %0" ::"r"(t0));
          t0 = *a__;
          a__ += N;
          asm volatile("vmul.vx v4, v16, %0" ::"r"(t1));
          t1 = *a__;
          a__ += N;
          asm volatile("vmul.vx v8, v16, %0" ::"r"(t2));
          t2 = *a__;
          a__ += N;
          asm volatile("vmul.vx v12, v16, %0" ::"r"(t3));
          t3 = *a__;
        } else {
          asm volatile("vmacc.vx v0, %0, v16" ::"r"(t0));
          t0 = *a__;
          a__ += N;
          asm volatile("vmacc.vx v4, %0, v16" ::"r"(t1));
          t1 = *a__;
          a__ += N;
          asm volatile("vmacc.vx v8, %0, v16" ::"r"(t2));
          t2 = *a__;
          a__ += N;
          asm volatile("vmacc.vx v12, %0, v16" ::"r"(t3));
          t3 = *a__;
        }

        a__ = a_ + ++n;

        if (n == N)
          break;

        asm volatile("vle32.v v16, (%0);" ::"r"(b__));
        b__ += P;

        asm volatile("vmacc.vx v0, %0, v20" ::"r"(t0));
        t0 = *a__;
        a__ += N;
        asm volatile("vmacc.vx v4, %0, v20" ::"r"(t1));
        t1 = *a__;
        a__ += N;
        asm volatile("vmacc.vx v8, %0, v20" ::"r"(t2));
        t2 = *a__;
        a__ += N;
        asm volatile("vmacc.vx v12, %0, v20" ::"r"(t3));
        t3 = *a__;
      }

      asm volatile("vmacc.vx v0, %0, v20" ::"r"(t0));
      asm volatile("vse32.v v0, (%0);" ::"r"(c__));
      c__ += P;
      asm volatile("vmacc.vx v4, %0, v20" ::"r"(t1));
      asm volatile("vse32.v v4, (%0);" ::"r"(c__));
      c__ += P;
      asm volatile("vmacc.vx v8, %0, v20" ::"r"(t2));
      asm volatile("vse32.v v8, (%0);" ::"r"(c__));
      c__ += P;
      asm volatile("vmacc.vx v12, %0, v20" ::"r"(t3));
      asm volatile("vse32.v v12, (%0);" ::"r"(c__));
    }

    p += gvl;
  }
}

// ---------------
// 8xVL
// ---------------

void matmul_8xVL(int32_t *c, const int32_t *a, const int32_t *b,
                 const unsigned int m_start, const unsigned int m_end,
                 const unsigned int N, const unsigned int P,
                 const unsigned int p_start, const unsigned int p_end) {

  unsigned int p = p_start;
  while (p < p_end) {
    // Calculate the vl
    size_t gvl;
    asm volatile("vsetvli %[gvl], %[vl], e32, m2, ta, ma"
                 : [gvl] "=r"(gvl)
                 : [vl] "r"(p_end - p));

    const int32_t *b_ = b + p;
    int32_t *c_ = c + p;

    for (unsigned int m = m_start; m < m_end; m += 8) {
      const int32_t *a_ = a + m * N;
      const int32_t *a__ = a_;

      asm volatile("vle32.v v18, (%0);" ::"r"(b_));
      const int32_t *b__ = b_ + P;

      int32_t *c__ = c_ + m * P;

      int32_t t0, t1, t2, t3, t4, t5, t6, t7;

      t0 = *a__;
      a__ += N;
      t1 = *a__;
      a__ += N;
      t2 = *a__;
      a__ += N;
      t3 = *a__;
      a__ += N;
      t4 = *a__;
      a__ += N;
      t5 = *a__;
      a__ += N;
      t6 = *a__;
      a__ += N;
      t7 = *a__;

      unsigned int n = 0;

      while (n < N) {
        a__ = a_ + ++n;

        asm volatile("vle32.v v20, (%0);" ::"r"(b__));
        b__ += P;

        if (n == 1) {
          asm volatile("vmul.vx v0, v18, %0" ::"r"(t0));
          t0 = *a__;
          a__ += N;
          asm volatile("vmul.vx v2, v18, %0" ::"r"(t1));
          t1 = *a__;
          a__ += N;
          asm volatile("vmul.vx v4, v18, %0" ::"r"(t2));
          t2 = *a__;
          a__ += N;
          asm volatile("vmul.vx v6, v18, %0" ::"r"(t3));
          t3 = *a__;
          a__ += N;
          asm volatile("vmul.vx v8, v18, %0" ::"r"(t4));
          t4 = *a__;
          a__ += N;
          asm volatile("vmul.vx v10, v18, %0" ::"r"(t5));
          t5 = *a__;
          a__ += N;
          asm volatile("vmul.vx v12, v18, %0" ::"r"(t6));
          t6 = *a__;
          a__ += N;
          asm volatile("vmul.vx v14, v18, %0" ::"r"(t7));
          t7 = *a__;
        } else {
          asm volatile("vmacc.vx v0, %0, v18" ::"r"(t0));
          t0 = *a__;
          a__ += N;
          asm volatile("vmacc.vx v2, %0, v18" ::"r"(t1));
          t1 = *a__;
          a__ += N;
          asm volatile("vmacc.vx v4, %0, v18" ::"r"(t2));
          t2 = *a__;
          a__ += N;
          asm volatile("vmacc.vx v6, %0, v18" ::"r"(t3));
          t3 = *a__;
          a__ += N;
          asm volatile("vmacc.vx v8, %0, v18" ::"r"(t4));
          t4 = *a__;
          a__ += N;
          asm volatile("vmacc.vx v10, %0, v18" ::"r"(t5));
          t5 = *a__;
          a__ += N;
          asm volatile("vmacc.vx v12, %0, v18" ::"r"(t6));
          t6 = *a__;
          a__ += N;
          asm volatile("vmacc.vx v14, %0, v18" ::"r"(t7));
          t7 = *a__;
        }

        a__ = a_ + ++n;

        if (n == N)
          break;

        asm volatile("vle32.v v18, (%0);" ::"r"(b__));
        b__ += P;

        asm volatile("vmacc.vx v0, %0, v20" ::"r"(t0));
        t0 = *a__;
        a__ += N;
        asm volatile("vmacc.vx v2, %0, v20" ::"r"(t1));
        t1 = *a__;
        a__ += N;
        asm volatile("vmacc.vx v4, %0, v20" ::"r"(t2));
        t2 = *a__;
        a__ += N;
        asm volatile("vmacc.vx v6, %0, v20" ::"r"(t3));
        t3 = *a__;
        a__ += N;
        asm volatile("vmacc.vx v8, %0, v20" ::"r"(t4));
        t4 = *a__;
        a__ += N;
        asm volatile("vmacc.vx v10, %0, v20" ::"r"(t5));
        t5 = *a__;
        a__ += N;
        asm volatile("vmacc.vx v12, %0, v20" ::"r"(t6));
        t6 = *a__;
        a__ += N;
        asm volatile("vmacc.vx v14, %0, v20" ::"r"(t7));
        t7 = *a__;
      }

      asm volatile("vmacc.vx v0, %0, v20" ::"r"(t0));
      asm volatile("vse32.v v0, (%0);" ::"r"(c__));
      c__ += P;
      asm volatile("vmacc.vx v2, %0, v20" ::"r"(t1));
      asm volatile("vse32.v v2, (%0);" ::"r"(c__));
      c__ += P;
      asm volatile("vmacc.vx v4, %0, v20" ::"r"(t2));
      asm volatile("vse32.v v4, (%0);" ::"r"(c__));
      c__ += P;
      asm volatile("vmacc.vx v6, %0, v20" ::"r"(t3));
      asm volatile("vse32.v v6, (%0);" ::"r"(c__));
      c__ += P;
      asm volatile("vmacc.vx v8, %0, v20" ::"r"(t4));
      asm volatile("vse32.v v8, (%0);" ::"r"(c__));
      c__ += P;
      asm volatile("vmacc.vx v10, %0, v20" ::"r"(t5));
      asm volatile("vse32.v v10, (%0);" ::"r"(c__));
      c__ += P;
      asm volatile("vmacc.vx v12, %0, v20" ::"r"(t6));
      asm volatile("vse32.v v12, (%0);" ::"r"(c__));
      c__ += P;
      asm volatile("vmacc.vx v14, %0, v20" ::"r"(t7));
      asm volatile("vse32.v v14, (%0);" ::"r"(c__));
    }

    p += gvl;
  }
}
