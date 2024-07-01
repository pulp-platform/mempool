// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/* This file handles the ATOMIC and CRITICAL constructs.  */

#include "encoding.h"
#include "libgomp.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

void GOMP_atomic_start() { gomp_hal_lock(&works.atomic_lock); }

void GOMP_atomic_end() { gomp_hal_unlock(&works.atomic_lock); }

void GOMP_critical_start() { gomp_hal_lock(&works.critical_lock); }

void GOMP_critical_end() { gomp_hal_unlock(&works.critical_lock); }
