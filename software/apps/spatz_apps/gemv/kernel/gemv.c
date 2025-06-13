// Copyright 2025 ETH Zurich and University of Bologna.
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

// Author: Navaneeth Kunhi Purayil, ETH Zurich <nkunhi@iis.ee.ethz.ch>
// Author: Diyou Shen,              ETH Zurich <dishen@iis.ee.ethz.ch>


#include "gemv.h"
#include "printf.h"

// This algorithm does not give good perforamnce, currently abandoned
void gemv_v32b_m4_unroll_M(float *a, float* b, float* c, uint32_t M, uint32_t M_core, uint32_t N) {
  unsigned int vl, avl = M_core;
  float *a_      = a;
  float *a_nextM = a_ + (M_core * N);
  float *b_      = b;
  float *c_      = c;

  asm volatile("vmv.s.x v4, zero");
  asm volatile("vmv.s.x v12, zero");

  do {
    asm volatile("vsetvli %0, %1, e32, m4, ta, ma" : "=r"(vl) : "r"(avl));
    for (uint32_t col = 0; col < N; col+=2) {
      // Load chunk a
      asm volatile("vle32.v v0, (%0)" ::"r"(a_));
      a_ += M;
      asm volatile("vle32.v v16, (%0)" ::"r"(a_nextM));
      a_nextM += M;

      // Two maccs can be done with same b
      asm volatile("vfmacc.vf v4, %0, v0" ::"f"(*b_));
      asm volatile("vfmacc.vf v20, %0, v0" ::"f"(*b_));
      b_++;


      asm volatile("vle32.v v8, (%0)" ::"r"(a_));
      a_ += M;
      asm volatile("vle32.v v24, (%0)" ::"r"(a_nextM));
      a_nextM += M;

      // Two maccs can be done with same b
      asm volatile("vfmacc.vf v4, %0, v0" ::"f"(*b_));
      asm volatile("vfmacc.vf v20, %0, v0" ::"f"(*b_));
      b_++;

    }
    asm volatile("vse32.v v4, (%0)" ::"r"(c_));
    avl -= vl;
    c_ += vl;
    b_ = b;
    a_ = a + avl;
  } while (avl > 0);
  
}

void gemv_v32b_m4(float *a, float* b, float* c, uint32_t M, uint32_t M_core, uint32_t N) {
  unsigned int vl, avl = M_core;
  float *a_ = a;
  float *b_ = b;
  float *c_ = c;
  
  do {
    asm volatile("vsetvli %0, %1, e32, m4, ta, ma" : "=r"(vl) : "r"(avl));
    for (uint32_t col = 0; col < N; col+=2) {
      // Load chunk a
      asm volatile("vle32.v v0, (%0)" ::"r"(a_));
      a_ += M;

      // Multiply and accumulate
      if (col == 0) {
        asm volatile("vfmul.vf v4, v0, %0" ::"f"(*b_));
      } else {
        asm volatile("vfmacc.vf v4, %0, v0" ::"f"(*b_));
      }
      b_++;

      // Load chunk a
      asm volatile("vle32.v v8, (%0)" ::"r"(a_));
      a_ += M;

      // Multiply and accumulate
      if (col == 0) {
        asm volatile("vfmul.vf v12, v8, %0" ::"f"(*b_));
      } else {
        asm volatile("vfmacc.vf v12, %0, v8" ::"f"(*b_));
      }
      b_++;

    }
    asm volatile("vfadd.vv v12, v12, v4");
    asm volatile("vse32.v v12, (%0)" ::"r"(c_));
    avl -= vl;
    c_ += vl;
    b_ = b;
    a_ = a + avl;
  } while (avl > 0);
  
}

void gemv_v16b_m4(__fp16 *a, __fp16* b, __fp16* c, uint32_t M, uint32_t M_core, uint32_t N) {
  unsigned int vl, avl = M_core;
  __fp16 *a_ = a;
  __fp16 *b_ = b;
  __fp16 *c_ = c;
  
  do {
    asm volatile("vsetvli %0, %1, e16, m4, ta, ma" : "=r"(vl) : "r"(avl));
    for (uint32_t col = 0; col < N; col+=2) {
      // Load chunk a
      asm volatile("vle16.v v0, (%0)" ::"r"(a_));
      a_ += M;
      
      // Load chunk a
      asm volatile("vle16.v v8, (%0)" ::"r"(a_));
      a_ += M;

      // Multiply and accumulate
      float t0;
      asm volatile("flh %[t], 0(%[b])" : [t] "=f"(t0) : [b] "r"(b_));
      if (col == 0) {
        asm volatile("vfmul.vf v4, v0, %0" ::"f"(t0));
      } else {
        asm volatile("vfmacc.vf v4, %0, v0" ::"f"(t0));
      }
      b_++;

      // Multiply and accumulate
      float t1;
      asm volatile("flh %[t], 0(%[b])" : [t] "=f"(t1) : [b] "r"(b_));
      if (col == 0) {
        asm volatile("vfmul.vf v12, v8, %0" ::"f"(t1));
      } else {
        asm volatile("vfmacc.vf v12, %0, v8" ::"f"(t1));
      }
      b_++;

    }
    asm volatile("vfadd.vv v12, v12, v4");
    asm volatile("vse16.v v12, (%0)" ::"r"(c_));
    avl -= vl;
    c_ += vl;
    b_ = b;
    a_ = a + avl;
  } while (avl > 0);
  
}
