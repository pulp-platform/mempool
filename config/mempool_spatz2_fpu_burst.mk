# Copyright 2021 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Author: Diyou Shen, ETH Zurich

###############
##  MemPool  ##
###############

# Number of cores
num_cores ?= 128

# Number of groups
num_groups ?= 4

# Number of cores per MemPool tile
num_cores_per_tile ?= 2

# L1 scratchpad banking factor
banking_factor ?= 4

# Radix for hierarchical AXI interconnect
axi_hier_radix ?= 17

# Number of AXI masters per group
axi_masters_per_group ?= 1

# Activate Spatz and RVV
spatz ?= 1

# Lenght of single vector register
vlen ?= 256

# Number of IPUs
n_ipu ?= 2

n_fpu ?= 2

# Deactivate the XpulpIMG extension
xpulpimg ?= 0

rvf ?= 1

# Enable TCDM Burst?
tcdm_burst ?= 1

# Enable Group Rsp?
group_rsp ?= 1

# Enable Parallel Burst Managers?
parallel_manager ?= 1

# L2 Banks/Channels
l2_size  ?= 4194304  # 400000
l2_banks ?= 4

# Number of DMA backends in each group
dmas_per_group ?= 1 # Brust Length = 16
