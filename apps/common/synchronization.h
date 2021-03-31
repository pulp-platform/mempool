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

#ifndef __SYNCHRONIZATION_H__
#define __SYNCHRONIZATION_H__

// Barrier functions
void mempool_barrier_init(uint32_t core_id, uint32_t num_cores);
void mempool_barrier(uint32_t num_cores, uint32_t cycles);

// Atomics

/**

 * Expose the atomic add instruction.
 *
 * @param   address     A pointer to an address on L2 memory to store the value.
 * @param   value       Value to add to the specified memory location.
 *
 * @return  Value previously stored in memory.
 */
static inline unsigned amo_add(void volatile *const address, unsigned value) {
  unsigned ret;
  asm volatile("" : : : "memory");
  asm volatile("amoadd.w  %0, %1, (%2)" : "=r"(ret) : "r"(value), "r"(address));
  asm volatile("" : : : "memory");
  return ret;
}

/**

 * Expose the atomic or instruction.
 *
 * @param   address     A pointer to an address on L2 memory to store the value.
 * @param   value       Value to add to the specified memory location.
 *
 * @return  Value previously stored in memory.
 */
static inline unsigned amo_or(void volatile *const address, unsigned value) {
  unsigned ret;
  asm volatile("" : : : "memory");
  asm volatile("amoor.w  %0, %1, (%2)" : "=r"(ret) : "r"(value), "r"(address));
  asm volatile("" : : : "memory");
  return ret;
}

#endif // __SYNCHRONIZATION_H__
