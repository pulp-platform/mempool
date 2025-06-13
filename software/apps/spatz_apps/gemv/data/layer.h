// Copyright 2025 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0 

#pragma once

#include <stdint.h>

typedef enum { FP64 = 8, FP32 = 4, FP16 = 2, FP8 = 1 } precision_t;

typedef struct gemv_layer_struct {
	uint32_t M;
	uint32_t N;

	precision_t dtype;
} gemv_layer;
