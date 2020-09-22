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

#include <stdint.h>
#include <string.h>

#include "encoding.h"
#include "kernel/synth.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

#define N 16

int32_t block_a[N] __attribute__((section(".l1_prio")));
int volatile error __attribute__((section(".l1")));

int main(int argc, char **argv) {
  uint32_t core_id = (uint32_t)argc;
  uint32_t num_cores = (uint32_t)argv;
  // Initialize barrier and synchronize
  mempool_barrier_init(core_id, num_cores);

  if (core_id == 0) {
    error = 0;
    for (int i = 0; i < N; ++i) {
      block_a[i] = 78459 + i;
    }
    power_profile(block_a);
  }

  // wait until all cores have finished
  mempool_barrier(num_cores, num_cores * 1000);

  return error;
}
