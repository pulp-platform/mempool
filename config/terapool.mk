# Copyright 2021 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Author: Matheus Cavalcante, ETH Zurich

################
##  TeraPool  ##
################

# Global Control
terapool ?= 1
flex_terapool ?= 1

# Number of cores
num_cores ?= 1024

# Number of groups
num_groups ?= 4

# Number of cores per Terapool tile
num_cores_per_tile ?= 8

# Number of sub groups per Terapool group
num_sub_groups_per_group ?= 4

# Number of shared divsqrt units per MemPool tile
# Defaults to 1 if xDivSqrt is activated
num_divsqrt_per_tile ?= 2

# L1 scratchpad banking factor
banking_factor ?= 4

# Access latency between remote groups
# Options: "7", "9" or "11":
remote_group_latency_cycles ?= 7

# Radix for hierarchical AXI interconnect
axi_hier_radix ?= 9

# Number of AXI masters per group
axi_masters_per_group ?= 4

# Number of DMA backends in each group
dmas_per_group ?= 4 # Brust Length = 16

# L2 Banks/Channels
l2_banks = 16
l2_size  ?= 16777216 # 1000000

# TeraPool w/ DAS
# Impacted memory size in byte per core by default
heap_seq_mem_size ?= 2048