// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/* Standard public APIs */

#pragma once

#include "kmp.h"
#include "runtime.h"
#include <stdint.h>

uint32_t omp_get_num_threads(void);
extern uint32_t omp_get_thread_num(void) { return mempool_get_core_id(); };
