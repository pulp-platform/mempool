# Copyright 2021 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Author: Matheus Cavalcante, ETH Zurich

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
axi_hier_radix ?= 20

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
rvd ?= 0
