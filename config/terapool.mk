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
num_groups ?= 8

# Number of cores per Terapool tile
num_cores_per_tile ?= 8

# Radix for hierarchical AXI interconnect
axi_hier_radix ?= 8

# Number of AXI masters per group
axi_masters_per_group ?= 2
