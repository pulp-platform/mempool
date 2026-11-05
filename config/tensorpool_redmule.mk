# Copyright 2026 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

################################
##  TensorPool, RedMulE 8x32  ##
################################

# Tensor engine (256 FMAs per engine, 512-bit port)
tensor_engine ?= redmule
redmule_height ?= 8
redmule_width ?= 32
redmule_regs ?= 3

# Two burst managers per tile, store queue, response VOQ
burst_manager_split ?= 2
store_queue_depth ?= 8
store_queue_pfe ?= 1
burst_port_voq ?= 1
burst_port_voq_entries ?= 8
burst_port_voq_cap ?= 10
burst_port_voq_pfe ?= 0

include $(MEMPOOL_DIR)/config/tensorpool.mk
