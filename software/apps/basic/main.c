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

// clang-format off

#include <stdint.h>
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"


#define UNALIGNED 1
#define VEC_LENGTH 33+UNALIGNED

uint8_t vector1[VEC_LENGTH] = {0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef, 0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef, 0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef, 0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef, 0x01, 0x23};
uint8_t vector2[VEC_LENGTH] = {0xfe, 0xdc, 0xba, 0x98, 0x76, 0x54, 0x32, 0x10, 0xfe, 0xdc, 0xba, 0x98, 0x76, 0x54, 0x32, 0x10, 0xfe, 0xdc, 0xba, 0x98, 0x76, 0x54, 0x32, 0x10, 0xfe, 0xdc, 0xba, 0x98, 0x76, 0x54, 0x32, 0x10, 0xfe, 0xdc};
uint8_t vector_res[VEC_LENGTH];

#define SLD_LENGTH_INIT 16
#define SLD_LENGTH 7

uint16_t vector_sld[SLD_LENGTH_INIT] = {0x0001, 0x0203, 0x0405, 0x0607, 0x0809, 0x0a0b, 0x0c0d, 0x0e0f, 0xf0e1, 0xd2c3, 0xb4a5, 0x9687, 0x7968, 0x5b4a, 0x3d2c, 0x1f0e};
uint16_t vector_sld_res[SLD_LENGTH];

int main() {
  const unsigned int cid = mempool_get_core_id();
  const unsigned int num_cores = mempool_get_core_count();
  //////////////////
  // Strip Mining //
  //////////////////

  // Stripmining loop
  int32_t remaining_elem = VEC_LENGTH-UNALIGNED;
  uint8_t *ptr_vec1 = vector1+UNALIGNED;
  uint8_t *ptr_vec2 = vector2+UNALIGNED;
  uint8_t *ptr_vec_res = vector_res+UNALIGNED;
  mempool_barrier_init(cid);
  
  while (remaining_elem > 0) {
    uint32_t actual_elem;
    asm volatile("vsetvli %0, %1, e8, m1, ta, ma" : "=r"(actual_elem) : "r"(remaining_elem));
    asm volatile("vle8.v v12, (%[vector1])" :: [vector1]"r"(ptr_vec1));
    asm volatile("vle8.v v13, (%[vector2])" :: [vector2]"r"(ptr_vec2));
    asm volatile("vadd.vv v14, v12, v13");
    asm volatile("vse8.v v14, (%[vector_res])" :: [vector_res]"r"(ptr_vec_res));
    remaining_elem -= actual_elem;
    ptr_vec1 += actual_elem;
    ptr_vec2 += actual_elem;
    ptr_vec_res += actual_elem;
  }
  // for (int i = UNALIGNED; i < VEC_LENGTH; i++) {
  //   if (vector1[i] + vector2[i] != vector_res[i]) return i+1;
  // }

  /////////////
  // VLE/VSE //
  /////////////
  if (cid == 0)
    printf("L/S\n");

  mempool_barrier(num_cores);
  for (int vstart = 0; vstart < VEC_LENGTH; vstart++) {
    // VLOAD

    asm volatile("vsetvli zero, %0, e8, m2, ta, ma" ::"r"(VEC_LENGTH));
    asm volatile("vmv.v.i v8, 0");
    asm volatile("csrrw zero, vstart, %0"::"r"(vstart));
    asm volatile("vle8.v v8, (%0)" :: "r"(vector1));
    asm volatile("vse8.v v8, (%0)" :: "r"(vector_res));

    for (int i = 0; i < vstart; i++) {
      if (vector_res[i] != 0) return i+1;
    }
    for (int i = vstart; i < VEC_LENGTH; i++) {
      if (vector1[i] != vector_res[i]) return i+1;
    }

    // VSTORE

    // Clear result vector
    for (int i = 0; i < VEC_LENGTH; i++) {
      vector_res[i] = 0;
    }

    asm volatile("vsetvli zero, %0, e8, m2, ta, ma" ::"r"(VEC_LENGTH));
    asm volatile("vle8.v v8, (%0)" :: "r"(vector1));
    asm volatile("csrrw zero, vstart, %0"::"r"(vstart));
    asm volatile("vse8.v v8, (%0)" :: "r"(vector_res));

    for (int i = 0; i < vstart; i++) {
      if (vector_res[i] != 0) return i+1;
    }
    for (int i = vstart; i < VEC_LENGTH; i++) {
      if (vector1[i] != vector_res[i]) return i+1;
    }
  }

  ////////////
  // VSLIDE //
  ////////////
  if (cid == 0)
    printf("VSlide\n");
  
  mempool_barrier(num_cores);
  for (int vstart = 0; vstart < 8; vstart++) {
    // Element to insert on vslide1up/down
    uint16_t elem_insert = 0xabff;

    // Vector slide1up
    asm volatile("vsetvli zero, %0, e16, m1, ta, ma" ::"r"(SLD_LENGTH));
    asm volatile("vle16.v v8, (%0)" :: "r"(vector_sld));
    asm volatile("csrrw zero, vstart, %0"::"r"(vstart));
    asm volatile("vslide1up.vx v9, v8, %0" :: "r"(elem_insert));
    asm volatile("vse16.v v9, (%0)" :: "r"(vector_sld_res));

    if (vstart == 0) {
      if (vector_sld_res[0] != elem_insert) return 1;
    }
    for (int i = vstart+(vstart == 0); i < SLD_LENGTH; i++) {
      if (vector_sld_res[i] != vector_sld[i-1]) return i+1;
    }

    // Vector slideup
    for (int sld_amt = 0; sld_amt < SLD_LENGTH; sld_amt++) {
      asm volatile("vsetvli zero, %0, e16, m1, ta, ma" ::"r"(SLD_LENGTH));
      asm volatile("vle16.v v10, (%0)" :: "r"(vector_sld));
      asm volatile("vmv.v.i v11, 0");
      asm volatile("csrrw zero, vstart, %0"::"r"(vstart));
      asm volatile("vslideup.vx v11, v10, %0" :: "r"(sld_amt));
      asm volatile("vse16.v v11, (%0)" :: "r"(vector_sld_res));

      for (int i = vstart; i < SLD_LENGTH; i++) {
        if (i < sld_amt) {
          if (vector_sld_res[i] != 0) return i+1;
        }
        if (i >= sld_amt) {
          if (vector_sld_res[i] != vector_sld[i-sld_amt]) return i+1;
        }
      }
    }

    // Vector slide1down
    asm volatile("vsetvli zero, %0, e16, m1, ta, ma" ::"r"(SLD_LENGTH));
    asm volatile("vle16.v v6, (%0)" :: "r"(vector_sld));
    asm volatile("csrrw zero, vstart, %0"::"r"(vstart));
    asm volatile("vslide1down.vx v7, v6, %0" :: "r"(elem_insert));
    asm volatile("vse16.v v7, (%0)" :: "r"(vector_sld_res));

    for (int i = vstart; i < SLD_LENGTH-1; i++) {
      if (vector_sld_res[i] != vector_sld[i+1]) return i+1;
    }
    if (vector_sld_res[SLD_LENGTH-1] != elem_insert) return SLD_LENGTH;

    // Vector slidedown
    for (int sld_amt = 0; sld_amt < SLD_LENGTH; sld_amt++) {
      asm volatile("vsetvli zero, %0, e16, m2, ta, ma" ::"r"(SLD_LENGTH_INIT));
      asm volatile("vle16.v v4, (%0)" :: "r"(vector_sld));
      asm volatile("vsetvli zero, %0, e16, m2, ta, ma" ::"r"(SLD_LENGTH));
      asm volatile("vmv.v.i v2, 0");
      asm volatile("csrrw zero, vstart, %0"::"r"(vstart));
      asm volatile("vslidedown.vx v2, v4, %0" :: "r"(sld_amt));
      asm volatile("vse16.v v2, (%0)" :: "r"(vector_sld_res));

      for (int i = vstart; i < SLD_LENGTH; i++) {
        if (i < 256-sld_amt) {
          if (vector_sld_res[i] != vector_sld[i+sld_amt]) return i+1;
        } else {
          if (vector_sld_res[i] != 0) return i+1;
        }
      }
    }
  }
  mempool_barrier(num_cores);

  return 0;
}

// clang-format on
