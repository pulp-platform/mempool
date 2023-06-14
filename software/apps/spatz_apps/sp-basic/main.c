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

// Author: Diyou Shen, ETH Zurich

// clang-format off

#include <stdint.h>
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

float res1[16], res2[16];
const float alpha = 0.123f;
static float vec1[16] = {0.035711680f, 0.84912932f, 0.93399322f, 0.67873514f, 0.75774014f, 0.74313247f, 0.39222702f, 0.65547788f, 0.17118669f, 0.70604610f, 0.031832848f, 0.27692297f, 0.046171390f, 0.097131781f, 0.82345784f, 0.69482863f};
static float vec2[16] = {0.31709948f, 0.95022207f, 0.034446079f, 0.43874437f, 0.38155845f, 0.76551682f, 0.79519993f, 0.18687260f, 0.48976439f, 0.44558620f, 0.64631301f, 0.70936483f, 0.75468665f, 0.27602509f, 0.67970270f, 0.65509802f};
static float vec3[16] = {0.35281116f, 1.7993515f, 0.96843928f, 1.1174796f, 1.1392986f, 1.5086493f, 1.1874269f, 0.84235048f, 0.66095108f, 1.1516323f, 0.67814589f, 0.98628783f, 0.80085802f, 0.37315688f, 1.5031605f, 1.3499267f};
static float vec4[16] = {0.043925366f, 1.04442906f, 1.14881166f, 0.83484422f, 0.93202037f, 0.91405294f, 0.48243923f, 0.80623779f, 0.21055963f, 0.86843670f, 0.039154403f, 0.34061525f, 0.056790810f, 0.119472091f, 1.01285314f, 0.85463921f};

int main() {

  int32_t remaining_elem = 16;
  const unsigned int cid = mempool_get_core_id();
  const unsigned int num_cores = mempool_get_core_count();
  int error = 0;

  float *ptr_vec1 = vec1;
  float *ptr_vec2 = vec2;
  float *ptr_vec_res1 = res1;
  float *ptr_vec_res2 = res2;

  mempool_barrier_init(cid);
  int32_t count = 0;

  while (remaining_elem > 0) {
    uint32_t actual_elem;

    asm volatile("vsetvli %0, %1, e32, m1, ta, ma" : "=r"(actual_elem) : "r"(remaining_elem));
    asm volatile("vle32.v v16, (%[vector1])" :: [vector1]"r"(ptr_vec1));
    asm volatile("vle32.v v17, (%[vector2])" :: [vector2]"r"(ptr_vec2));
    asm volatile("vfadd.vv v14, v16, v17");
    asm volatile("vfmul.vf v15, v16, %0" ::"f"(alpha));
    asm volatile("vse32.v v14, (%[vector_res])" :: [vector_res]"r"(ptr_vec_res1));
    asm volatile("vse32.v v15, (%[vector_res])" :: [vector_res]"r"(ptr_vec_res2));

    remaining_elem -= actual_elem;
    ptr_vec1 += actual_elem;
    ptr_vec2 += actual_elem;
    ptr_vec_res1 += actual_elem;
    count ++;
  }
  const float ub = 0.1f;
  const float lb = -0.1f;
  float diff;

  // mempool_barrier(num_cores);
  // if (cid == 0) {
  //   printf("CHECK VFADD\n");
  // }
  mempool_barrier(num_cores);

  if (cid == 0) {
    for (int i = 0; i < 16; i++) {
      if (vec3[i] != res1[i]) {
        printf("error: %d\n", i);
        // return 1;
      }
    }
    printf("count:%d\n", count);
  }
  mempool_barrier(num_cores);

  if (cid == 0) {
    printf("CHECK VFMUL\n");
  
    for (int i = 0; i < 16; i++) {
      // diff = vec4[i] - res2[i];
      if (vec4[i] != res2[i]) {
        printf("error: %d", i);
        // return i+1;
      }
    }
  }

  // if (cid == 0)
  //   printf("COREECT\n");
  mempool_barrier(num_cores);

  return 0;
}

// clang-format on
