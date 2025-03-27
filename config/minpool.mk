# Copyright 2021 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Author: Matheus Cavalcante, ETH Zurich

###############
##  MinPool  ##
###############

# Number of cores
num_cores ?= 16

# Number of groups
num_groups ?= 4

# Number of cores per MemPool tile
num_cores_per_tile ?= 4

# Number of shared divsqrt units per MemPool tile
# Defaults to 1 if xDivSqrt is activated
num_divsqrt_per_tile ?= 1

# FlooNoC configuration
num_directions ?= 5
num_x ?= 2
topology ?= 2dmesh
routing_algorithm ?= xy
req_remapping ?= 0
resp_remapping ?= 0
num_virtual_channel ?= 1

# Per tile, separate the NoC read and read/write req channels, rd = hdr, wr = har+payload, rd/wr = hdr+payload
noc_req_rd_channel_num ?= 0
noc_req_rdwr_channel_num ?= 1
noc_req_wr_channel_num ?= 0
noc_resp_channel_num ?= 1

# router buffer configuration
noc_router_input_fifo_dep ?= 2
noc_router_output_fifo_dep ?= 2

# L1 scratchpad banking factor
banking_factor ?= 4

#########################
##  AXI configuration  ##
#########################
# AXI bus data width (in bits)
axi_data_width ?= 256

# Read-only cache line width in AXI interconnect (in bits)
ro_line_width ?= 256

# Radix for hierarchical AXI interconnect
axi_hier_radix ?= 2

# Number of AXI masters per group
axi_masters_per_group ?= 1

# Number of DMA backends in each group
dmas_per_group ?= 1 # Brust Length = 16

# L2 Banks/Channels
l2_size  ?= 4194304  # 400000
l2_banks ?= 4
axi_width_interleaved ?= 2
