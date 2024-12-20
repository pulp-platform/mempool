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
xpulpimg ?= 1

# Enable FPU extensions
zfinx ?= 1

# Enable FPU extensions
zquarterinx ?= 0

# DivSqrt deactivated by default
xDivSqrt ?= 0

# DRAMsys co-simulation: dram/sram
l2_sim_type ?= sram
dram_axi_width_interleaved ?= 16

# Enable SPM bank id remapping inside of each tile
spm_bank_id_remap ?= 0

# Enable tile id remapping inside of each group
tile_id_remap ?= 0

# Enable the spm access pattern profiling
spm_profiling ?= 0

# Enable the interconnect access pattern profiling
noc_profiling ?= 0