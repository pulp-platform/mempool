# Copyright 2021 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

########################
##  Systolic MemPool  ##
########################

# Number of cores
num_cores ?= 256

# Number of groups
num_groups ?= 4

# Number of cores per MemPool tile
num_cores_per_tile ?= 4

# Number of shared divsqrt units per MemPool tile
# Defaults to 1 if xDivSqrt is activated
num_divsqrt_per_tile ?= 1

# L1 scratchpad banking factor
banking_factor ?= 4

# Radix for hierarchical AXI interconnect
axi_hier_radix ?= 20

# Number of AXI masters per group
axi_masters_per_group ?= 1

# Numer of AXI masters for all clusters
axi_masters_all_clusters ?= 4

# Size of sequential memory per core (in bytes)
# (must be a power of two)
seq_mem_size ?= 1024

#############################
##  Xqueues configuration  ##
#############################

# Xqueue extension's queue size (in queue entries)
# in each memory bank (assume banking factor of 4)
xqueue_size ?= 4
