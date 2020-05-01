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

// Author: Matheus Cavalcante, ETH Zurich

#include "printf.h"
#include <stdint.h>
#include <string.h>
#include "encoding.h"

volatile uint32_t atomic __attribute__ ((section (".l1")));

extern volatile uint32_t tcdm_start_address_reg;
extern volatile uint32_t tcdm_end_address_reg;

int main(int argc, char **argv) {
    uint32_t coreid = (uint32_t) argc;
    uint32_t num_cores = (uint32_t) argv;
    //TODO(sriedel): This is a hack, to be fixed when MemPool has a fence mechanism.
    if (coreid == 0)
      atomic = 0;

    while (atomic != coreid);

    printf("Core %d says Hello!\n", coreid);
    // increment mutex
    //__atomic_add_fetch(&atomic, 1, __ATOMIC_RELAXED);
    atomic++;
    // wait until all cores have finished
    while (atomic != num_cores);
    return 0;
}
