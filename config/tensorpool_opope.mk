# Copyright 2026 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

################################
##  TensorPool, O-POPE 16x16  ##
################################

# Tensor engine (256 FMAs per engine, 512-bit port)
tensor_engine ?= opope
redmule_height ?= 16
redmule_width ?= 16
# O-POPE needs PIPE_REGS = X_REGBUFFER_DEPTH * W_REGBUFFER_DEPTH
redmule_regs ?= 4
opope_regb_x_depth ?= 2
opope_regb_w_depth ?= 2

# Two burst managers per tile, store queue, response VOQ
burst_manager_split ?= 2
store_queue_depth ?= 8
store_queue_pfe ?= 1
burst_port_voq ?= 1
burst_port_voq_entries ?= 8
burst_port_voq_cap ?= 10
burst_port_voq_pfe ?= 0

include $(MEMPOOL_DIR)/config/tensorpool.mk
