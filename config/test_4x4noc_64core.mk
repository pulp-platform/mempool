# ============================================================================
#  Copyright 2025 ETH Zurich and University of Bologna.
#  Licensed under the Apache License, Version 2.0, see LICENSE for details.
#  SPDX-License-Identifier: Apache-2.0
#
#  Author: Yichao Zhang, ETH Zurich
# ============================================================================

###########################
## 1. Architecture Config
###########################

# Global Control
terapool ?= 1

# Number of cores
num_cores ?= 64

# Number of groups
num_groups ?= 16

# Number of cores per MemPool tile
num_cores_per_tile ?= 2

# L1 scratchpad banking factor
banking_factor ?= 16

# Number of shared divsqrt units per MemPool tile
# Defaults to 1 if xDivSqrt is activated
num_divsqrt_per_tile ?= 1

#####################
## 2. NoC Config
#####################

# FlooNoC configuration
num_directions ?= 5
num_x          ?= 4

# Topology
# 0: 2D mesh, 1: torus
noc_topology ?= 0

# Routing algorithm
# 0: xy, 1: odd-even, 2: o1
noc_routing_algorithm ?= 0

# NoC remapping configuration
# 0: no remapping, 1: req remapping, 2: resp remapping 3: req+resp remapping
noc_router_remapping ?= 0

# Virtual channel number
noc_virtual_channel_num ?= 1

# Channel configuration mode (internal control only)
# Options: baseline, narrow, enhanced
channel_config_mode := baseline  # Current MinPool setting

# Channel configuration based on selected mode
ifeq ($(channel_config_mode), baseline)
noc_req_rd_channel_num   ?= 0
noc_req_rdwr_channel_num ?= 2
noc_req_wr_channel_num   ?= 0
noc_resp_channel_num     ?= 2

else ifeq ($(channel_config_mode), narrow)
noc_req_rd_channel_num   ?= 1
noc_req_rdwr_channel_num ?= 1
noc_req_wr_channel_num   ?= 0
noc_resp_channel_num     ?= 2

else ifeq ($(channel_config_mode), enhanced)
noc_req_rd_channel_num   ?= 1
noc_req_rdwr_channel_num ?= 1
noc_req_wr_channel_num   ?= 0
noc_resp_channel_num     ?= 3

else
$(error Unsupported channel_config_mode: $(channel_config_mode))
endif

# Print configuration info for debugging
$(info [DEBUG:][noc_req_rd_channel_num]----$(noc_req_rd_channel_num))
$(info [DEBUG:][noc_req_rdwr_channel_num]--$(noc_req_rdwr_channel_num))
$(info [DEBUG:][noc_req_wr_channel_num]----$(noc_req_wr_channel_num))
$(info [DEBUG:][noc_resp_channel_num]------$(noc_resp_channel_num))

# Router buffer configuration
noc_router_input_fifo_dep  ?= 2
noc_router_output_fifo_dep ?= 2

# Router remapping configuration
noc_router_remap_group_size ?= 2

###########################
## 3. AXI and DMA Config
###########################

# Radix for hierarchical AXI interconnect
# Typically: num_cores_per_tile * num_tiles_per_group + num_dma_per_groups
axi_hier_radix ?= 5

# Number of AXI masters per group
axi_masters_per_group ?= 1

# Number of DMA backends in each group
dmas_per_group ?= 1  # Burst Length = 16

# L2 Banks/Channels
l2_size  ?= 16777216  # 1000000
l2_banks ?= 16
