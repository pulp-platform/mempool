# Copyright 2021 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Author: Samuel Riedel, ETH Zurich
#         Matheus Cavalcante, ETH Zurich

######################
##  MemPool flavor  ##
######################

# Choose a MemPool flavor, either "minpool" or "mempool".
# Check the README for more details
ifndef config
  ifdef MEMPOOL_CONFIGURATION
    config := $(MEMPOOL_CONFIGURATION)
  else
    # Default configuration, if neither `config` nor `MEMPOOL_CONFIGURATION` was found
    config := mempool
  endif
endif
include $(MEMPOOL_DIR)/config/$(config).mk

#############################
##  Address configuration  ##
#############################

# Boot address (in dec)
boot_addr ?= 2684354560 # A0000000

# L2 memory configuration (in dec)
l2_base  ?= 2147483648 # 80000000

# L1 size per bank (in dec)
l1_bank_size ?= 1024

# Size of sequential memory per core (in bytes)
# (must be a power of two)
seq_mem_size ?= 512

# Size of stack in sequential memory per core (in bytes)
stack_size ?= 512

#########################
##  AXI configuration  ##
#########################
# AXI bus data width (in bits)
axi_data_width ?= 512

# Read-only cache line width in AXI interconnect (in bits)
ro_line_width ?= 512

#############################
##  Xqueues configuration  ##
#############################

# XQueue extension's queue size in each memory bank (in words)
xqueue_size ?= 0

################################
##  Optional functionalities  ##
################################

# Enable the XpulpIMG extension
xpulpimg ?= 0

# DivSqrt deactivated by default
xDivSqrt ?= 0

# This parameter is only used for TeraPool configurations
num_sub_groups_per_group ?= 1
remote_group_latency_cycles ?= 7

# DRAMsys co-simulation: dram/sram
l2_sim_type ?= sram
dram_axi_width_interleaved ?= 16

# Deactivate the FPU
n_fpu ?= 0

# Deactivate single-precision (rvf) and double-precision (rvd) floating-point
rvf ?= 0
rvd ?= 0

# Enable TCDM Burst?
tcdm_burst ?= 0

# Enable Group Rsp?
group_rsp ?= 0

# Enable Parallel Burst Managers?
parallel_manager ?= 0
