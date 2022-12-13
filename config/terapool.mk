# Copyright 2021 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Author: Matheus Cavalcante, ETH Zurich

################
##  TeraPool  ##
################

# Number of cores
num_cores ?= 1024

# Number of groups
num_groups ?= 4

# Number of cores per Terapool tile
num_cores_per_tile ?= 8

# Number of sub groups per Terapool group
num_sub_groups_per_group ?= 4

# L1 scratchpad banking factor
banking_factor ?= 4

# Radix for hierarchical AXI interconnect
axi_hier_radix ?= 10

# Number of AXI masters per group
axi_masters_per_group ?= 4

# Number of DMA backends in each group
dmas_per_group ?= 8