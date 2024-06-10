# Copyright 2021 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Author: Samuel Riedel, ETH Zurich

###############
##  MemPool  ##
###############

# Number of cores
num_cores ?= 32

# Number of groups
num_groups ?= 8

# Number of clusters
num_clusters ?= 2

# Number of cores per MemPool tile
num_cores_per_tile ?= 4

# Number of shared divsqrt units per MemPool tile
# Defaults to 1 if xDivSqrt is activated
num_divsqrt_per_tile ?= 1

# L1 scratchpad banking factor
banking_factor ?= 4

#########################
##  AXI configuration  ##
#########################
# AXI bus data width (in bits)
axi_data_width ?= 256

# Read-only cache line width in AXI interconnect (in bits)
ro_line_width ?= 256

# Number of DMA backends in each group
dmas_per_group ?= 1

# Radix for hierarchical AXI interconnect
axi_hier_radix ?= 2

# Number of AXI masters per group
axi_masters_per_group ?= 1

# Numer of AXI masters for all clusters
axi_masters_all_clusters ?= 2
