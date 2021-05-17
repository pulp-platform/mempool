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

# L1 scratchpad banking factor
banking_factor ?= 4

# Radix for hierarchical AXI interconnect
axi_hier_radix ?= 16

# Number of AXI masters per group
axi_masters_per_group ?= 1

# Size of sequential memory per core (in bytes)
# (must be a power of two)
seq_mem_size ?= 2048

#############################
##  Xqueues configuration  ##
#############################

# Hardware queues for systolic (atomic ISA extension in TCDM adapter)
xqueue ?= 1

# Systolic queues size (assume banking factor of 4) for:
# - software queues emulation (size measured in queue entries)
# - hardware xqueue's queue in each memory bank (size measured in words)
xqueue_size ?= 4
