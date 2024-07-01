// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/* Standard public APIs */

#ifndef __OMP_H__
#define __OMP_H__

#include "stdint.h"

/* parallel.c */
extern uint32_t omp_get_num_threads(void);
extern uint32_t omp_get_thread_num(void);

#endif /* __OMP_H__ */
