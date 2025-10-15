# Copyright 2021 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Author: Marco Bertuletti, ETH Zurich

##################
##  TensorPool  ##
##################

# Number of cores
num_cores ?= 400

# Number of groups
num_groups ?= 4

# Number of cores per TensorPool tile
num_cores_per_tile ?= 8

# Number of sub groups per Tensorpool group
num_sub_groups_per_group ?= 4

# Number of shared divsqrt units per MemPool tile
# Defaults to 1 if xDivSqrt is activated
num_divsqrt_per_tile ?= 1

# L1 scratchpad banking factor
banking_factor ?= 4

# Access latency between remote groups
# Options: "7", "9" or "11":
remote_group_latency_cycles ?= 9

# Radix for hierarchical AXI interconnect
axi_hier_radix ?= 17

# Number of AXI masters per group
axi_masters_per_group ?= 4

# Number of DMA backends in each group
dmas_per_group ?= 4 # Burst Length = 16

# L2 Banks/Channels
l2_banks ?= 4
l2_size  ?= 4194304  # 400000

#############################
##  RedMulE Configuration  ##
#############################

# RedMulE Tiles must be multiple of Group number (MemPool) or SubGroup number (TeraPool)
num_redmule_tiles ?= 16

# RedMulE engine size
redmule_height ?= 16
redmule_width ?= 16
redmule_regs ?= 3
