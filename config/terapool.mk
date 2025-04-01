# Copyright 2024 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Author: Yichao Zhang, ETH Zurich

################
##  TeraPool  ##
################

# Global Control
terapool ?= 1

# Number of cores
num_cores ?= 1024

# Number of groups
num_groups ?= 16

# Number of cores per Terapool tile
num_cores_per_tile ?= 4

# Number of shared divsqrt units per MemPool tile
# Defaults to 1 if xDivSqrt is activated
num_divsqrt_per_tile ?= 2

# FlooNoC configuration
num_directions ?= 5
num_x ?= 4
noc_topology ?= 0				# 0: 2D mesh, 1: torus
noc_routing_algorithm ?= 0		# 0: xy, 1: odd-even, 2: o1
noc_router_remapping ?= 0		# 0: no remapping, 1: req remapping, 2: resp remapping 3: req+resp remapping
noc_virtual_channel_num ?= 1

# Per tile, separate the NoC read and read/write req channels, rd = hdr, wr = har+payload, rd/wr = hdr+payload
# baseline
noc_req_rd_channel_num ?= 0
noc_req_rdwr_channel_num ?= 2

# reduced link count
# noc_req_rd_channel_num ?= 1
# noc_req_rdwr_channel_num ?= 1

# enhanced read link
# noc_req_rd_channel_num ?= 2
# noc_req_rdwr_channel_num ?= 1

noc_req_wr_channel_num ?= 0
noc_resp_channel_num ?= 2

# router buffer configuration
noc_router_input_fifo_dep ?= 2
noc_router_output_fifo_dep ?= 2

# router remapping configuration
noc_router_remap_group_size ?= 8

# L1 scratchpad banking factor
banking_factor ?= 4

# Radix for hierarchical AXI interconnect
axi_hier_radix ?= 17

# Number of AXI masters per group
axi_masters_per_group ?= 1

# Number of DMA backends in each group
dmas_per_group ?= 1 # Brust Length = 16

# L2 Banks/Channels
l2_size  ?= 16777216  # 1000000
l2_banks ?= 16
axi_width_interleaved ?= 16
