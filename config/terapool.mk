# Copyright 2024 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Author: Yichao Zhang, ETH Zurich

################
##  TeraPool  ##
################

# Global Control
terapool ?= 1

# Number of cores
num_cores ?= 1024

# Number of groups
num_groups ?= 16

# Number of cores per Terapool tile
num_cores_per_tile ?= 4

# Number of shared divsqrt units per MemPool tile
# Defaults to 1 if xDivSqrt is activated
num_divsqrt_per_tile ?= 2

# FlooNoC configuration
num_remote_ports_per_tile ?= 5
num_directions ?= 5
num_x ?= 4

# L1 scratchpad banking factor
banking_factor ?= 4

# Radix for hierarchical AXI interconnect
axi_hier_radix ?= 17

# Number of AXI masters per group
axi_masters_per_group ?= 1

# Number of DMA backends in each group
dmas_per_group ?= 1 # Brust Length = 16

# L2 Banks/Channels
l2_banks = 16
l2_size  ?= 16777216 # 1000000
