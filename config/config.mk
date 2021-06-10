# Copyright 2021 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Author: Samuel Riedel, ETH Zurich
#         Matheus Cavalcante, ETH Zurich

# Boot address (in hex)
boot_addr ?= A0000000

# Number of cores
num_cores ?= 256

# Number of cores per MemPool tile
num_cores_per_tile ?= 4

# Xpulpimg extension enabled?
xpulpimg ?= 1

# L2 memory configuration (in hex)
l2_base ?= 80000000
l2_size ?= 10000
