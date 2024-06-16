// Copyright 2024 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "barrier.hpp"

namespace kmp {
Barrier::Barrier(kmp_int32 numThreads) : barrier(0), generation(0), numThreads(numThreads) {}

Barrier::~Barrier() { DEBUG_PRINT("Destroying barrier at %p\n", this); }

}; // namespace kmp
