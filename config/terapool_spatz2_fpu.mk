# Copyright 2021 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Author: Matheus Cavalcante, ETH Zurich

################
##  TeraPool  ##
################

# Global Control
terapool ?= 1

# Number of cores
num_cores ?= 512

# Number of groups
num_groups ?= 4

# Number of cores per Terapool tile
num_cores_per_tile ?= 4

# Number of sub groups per Terapool group
num_sub_groups_per_group ?= 4

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
dmas_per_group ?= 4

# L2 Banks/Channels
l2_banks = 16

# Makefile RTL Filtering Control
subgroup_rtl = 1

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
