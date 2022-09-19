# Copyright 2021 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Author: Matheus Cavalcante, ETH Zurich

###################
##  MinPool FPU  ##
###################

# Number of cores
num_cores ?= 16

# Number of groups
num_groups ?= 4

# Number of cores per MemPool tile
num_cores_per_tile ?= 4

# L1 scratchpad banking factor
banking_factor ?= 4

# Number of DMA backends in each group
dmas_per_group ?= 1

# Radix for hierarchical AXI interconnect
axi_hier_radix ?= 2

# Number of AXI masters per group
axi_masters_per_group ?= 1

# Activate the FPU
fpu ?= 1

