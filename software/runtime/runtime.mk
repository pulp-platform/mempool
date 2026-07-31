# Copyright 2021 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Author: Samuel Riedel, ETH Zurich
#         Matheus Cavalcante, ETH Zurich
#         Marco Bertuletti, ETH Zurich

SHELL = /usr/bin/env bash

ROOT_DIR           := $(patsubst %/,%, $(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
MEMPOOL_DIR        := $(shell git rev-parse --show-toplevel 2>/dev/null || echo $$MEMPOOL_DIR)

# Include configuration
include $(MEMPOOL_DIR)/config/config.mk

# Python version
python             ?= python3

INSTALL_DIR        ?= $(MEMPOOL_DIR)/install
GCC_INSTALL_DIR    ?= $(INSTALL_DIR)/riscv-gcc
LLVM_INSTALL_DIR   ?= $(INSTALL_DIR)/llvm
OMP_DIR            ?= $(ROOT_DIR)/omp
HALIDE_DIR         ?= $(ROOT_DIR)/halide
KERNELS_DIR        ?= $(abspath $(ROOT_DIR)/../kernels)
DATA_DIR           ?= $(abspath $(ROOT_DIR)/../data)
REDMULE_DIR        ?= $(abspath $(MEMPOOL_DIR)/hardware/deps/redmule/sw)

COMPILER           ?= gcc
XPULPIMG           ?= $(xpulpimg)
ZFINX              ?= $(zfinx)
XDIVSQRT	         ?= $(xDivSqrt)

RISCV_XLEN         ?= 32
RISCV_ABI          ?= ilp32
RISCV_TARGET       ?= riscv$(RISCV_XLEN)-unknown-elf

###############################################################################
# GCC Toolchain                                                               #
###############################################################################

ifeq ($(COMPILER),gcc)
RISCV_PREFIX       ?= $(GCC_INSTALL_DIR)/bin/$(RISCV_TARGET)-
RISCV_CC           ?= $(RISCV_PREFIX)gcc
RISCV_CXX          ?= $(RISCV_PREFIX)g++
RISCV_OBJDUMP      ?= $(RISCV_PREFIX)objdump

# GCC compiler -march
ifeq ($(XPULPIMG),1)
RISCV_ARCH         ?= rv$(RISCV_XLEN)imaXpulpimg
RISCV_ARCH_AS      ?= $(RISCV_ARCH)
# Define __XPULPIMG if the extension is active
DEFINES            += -D__XPULPIMG
else
RISCV_ARCH_AS      ?= rv$(RISCV_ARCH)ima
endif

###############################################################################
# LLVM Toolchain                                                              #
###############################################################################

else
RISCV_PREFIX       ?= $(LLVM_INSTALL_DIR)/bin/llvm-
RISCV_CC           ?= $(LLVM_INSTALL_DIR)/bin/clang
RISCV_CXX          ?= $(LLVM_INSTALL_DIR)/bin/clang++
RISCV_OBJDUMP      ?= $(RISCV_PREFIX)objdump

# LLVM compiler -march
RISCV_ARCH         ?= rv$(RISCV_XLEN)ima
ifeq ($(ZFINX), 1)
RISCV_ARCH         := $(RISCV_ARCH)_zfinx
RISCV_ARCH         := $(RISCV_ARCH)_zhinx
RISCV_ARCH         := $(RISCV_ARCH)_zquarterinx
RISCV_ARCH         := $(RISCV_ARCH)_zvechalfinx
RISCV_ARCH         := $(RISCV_ARCH)_zvecquarterinx
RISCV_ARCH         := $(RISCV_ARCH)_zexpauxvechalfinx
RISCV_ARCH         := $(RISCV_ARCH)_zexpauxvecquarterinx
endif
ifeq ($(XPULPIMG), 1)
RISCV_ARCH         := $(RISCV_ARCH)_xpulppostmod
RISCV_ARCH         := $(RISCV_ARCH)_xpulpmacsi
RISCV_ARCH         := $(RISCV_ARCH)_xpulpvect
RISCV_ARCH         := $(RISCV_ARCH)_xpulpvectshufflepack
endif
RISCV_ARCH         := $(RISCV_ARCH)_xmempool
endif

###############################################################################
# RISCV binutils                                                              #
###############################################################################

RISCV_OBJCOPY      ?= $(RISCV_PREFIX)objcopy
RISCV_AS           ?= $(RISCV_PREFIX)as
RISCV_AR           ?= $(RISCV_PREFIX)ar
RISCV_LD           ?= $(RISCV_PREFIX)ld
RISCV_STRIP        ?= $(RISCV_PREFIX)strip

###############################################################################
# Compiler Definitions                                                        #
###############################################################################

DEFINES += -DPRINTF_DISABLE_SUPPORT_FLOAT -DPRINTF_DISABLE_SUPPORT_LONG_LONG -DPRINTF_DISABLE_SUPPORT_PTRDIFF_T
DEFINES += -DNUM_CORES=$(num_cores)
DEFINES += -DLOG2_NUM_CORES=$(shell echo "l($(num_cores))/l(2)" | bc -l | awk '{printf("%d", $$1)}')
DEFINES += -DNUM_GROUPS=$(num_groups)
DEFINES += -DNUM_CORES_PER_TILE=$(num_cores_per_tile)
DEFINES += -DBANKING_FACTOR=$(banking_factor)
DEFINES += -DNUM_BANKS=$(shell awk 'BEGIN{print $(banking_factor)*$(num_cores)}')
DEFINES += -DNUM_CORES_PER_GROUP=$(shell awk 'BEGIN{print int($(num_cores)/$(num_groups))}')
DEFINES += -DNUM_TILES_PER_GROUP=$(shell awk 'BEGIN{print int($(num_cores)/$(num_cores_per_tile))}')
DEFINES += -DLOG2_NUM_CORES_PER_TILE=$(shell awk 'BEGIN{print log($(num_cores_per_tile))/log(2)}')
DEFINES += -DBOOT_ADDR=$(boot_addr)
DEFINES += -DL1_BANK_SIZE=$(l1_bank_size)
DEFINES += -DL2_BASE=$(l2_base)
DEFINES += -DL2_SIZE=$(l2_size)
DEFINES += -DSEQ_MEM_SIZE=$(seq_mem_size)
DEFINES += -DLOG2_SEQ_MEM_SIZE=$(shell awk 'BEGIN{print log($(seq_mem_size))/log(2)}')
DEFINES += -DSTACK_SIZE=$(stack_size)
DEFINES += -DLOG2_STACK_SIZE=$(shell awk 'BEGIN{print log($(stack_size))/log(2)}')
DEFINES += -DXQUEUE_SIZE=$(xqueue_size)
DEFINES += -DNUM_REDMULE_TILES=$(num_redmule_tiles)
DEFINES += -DREDMULE_H=$(redmule_height)
DEFINES += -DREDMULE_P=$(redmule_regs)
ifdef terapool
DEFINES += -DNUM_SUB_GROUPS_PER_GROUP=$(num_sub_groups_per_group)
DEFINES += -DNUM_CORES_PER_SUB_GROUP=$(shell awk 'BEGIN{print ($(num_cores)/$(num_groups))/$(num_sub_groups_per_group)}')
DEFINES += -DNUM_TILES_PER_SUB_GROUP=$(shell awk 'BEGIN{print ($(num_cores)/$(num_groups))/$(num_cores_per_tile)/$(num_sub_groups_per_group)}')
endif
ifeq ($(XDIVSQRT), 1)
DEFINES += -D__XDIVSQRT
endif

###############################################################################
# Compiler Flags                                                              #
###############################################################################

# Specify cross compilation target. This can be omitted if LLVM is built with riscv as default target
RISCV_LLVM_TARGET  ?= --target=$(RISCV_TARGET) --sysroot=$(GCC_INSTALL_DIR)/$(RISCV_TARGET) --gcc-toolchain=$(GCC_INSTALL_DIR)

RISCV_WARNINGS           += -Wunused-variable -Wconversion -Wall -Wextra # -Werror
RISCV_FLAGS_COMMON_TESTS ?= -march=$(RISCV_ARCH) -mabi=$(RISCV_ABI) -I$(ROOT_DIR) -I$(REDMULE_DIR) -I$(KERNELS_DIR) -I$(DATA_DIR) -static
RISCV_FLAGS_COMMON       ?= $(RISCV_FLAGS_COMMON_TESTS) -g -std=gnu99 -O3  -fno-builtin-memcpy -fno-builtin-memset -ffast-math -fno-common -fno-builtin-printf $(DEFINES) $(RISCV_WARNINGS)
RISCV_FLAGS_GCC          ?= -mcmodel=medany -Wa,-march=$(RISCV_ARCH_AS) -mtune=mempool -fno-tree-loop-distribute-patterns # -falign-loops=32 -falign-jumps=32
RISCV_FLAGS_LLVM         ?= -mcmodel=small -mcpu=mempool-rv32 -mllvm -misched-topdown -menable-experimental-extensions
RISCV_OBJDUMP_FLAGS_GCC  := --disassembler-option="march=$(RISCV_ARCH_AS)"
RISCV_OBJDUMP_FLAGS_LLVM := --mcpu=mempool-rv32 --mattr=+m,+a,+xpulpmacsi,+xpulppostmod,+xpulpvect,+xpulpvectshufflepack,+zfinx

# FlexCluster multi-cluster runtime integration
ifeq ($(MULTI_CLUSTER),true)
	MULTI_CLUSTER_DIR  := $(ROOT_DIR)/multi_cluster
	DEFINES            += -DMULTI_CLUSTER -DMEMPOOL_CLUSTER_UNIT
	RISCV_FLAGS_COMMON += -I$(MULTI_CLUSTER_DIR)/include
	# The FlexCluster architecture headers are generated from the selected
	# `config` so they always track the chosen hardware configuration.
	MC_ARCH_CONFIG   := $(MULTI_CLUSTER_DIR)/configs/arch_$(config).py
	MC_ARCH_HDR      := $(MULTI_CLUSTER_DIR)/include/mc_cluster_arch.h
	MC_ARCH_INC      := $(MULTI_CLUSTER_DIR)/include/mc_cluster_arch.inc
	ifeq ($(wildcard $(MC_ARCH_CONFIG)),)
		$(error No MCluster arch config for config='$(config)'. Multi-cluster supports: mempool minpool tensorpool terapool)
	endif
	# Compilation must wait for the headers to be (re)generated.
	MC_HDR_DEP := $(MC_ARCH_HDR) $(MC_ARCH_INC)
endif

# Enable soft-divsqrt when the hardware is not supported.
ifeq ($(XDIVSQRT), 0)
RISCV_FLAGS_LLVM_TESTS   := $(RISCV_FLAGS_LLVM)
RISCV_FLAGS_LLVM         += -mno-fdiv
RISCV_OBJDUMP_FLAGS_LLVM := $(RISCV_OBJDUMP_FLAGS_LLVM),+nofdiv
endif

# GCC Flags
ifeq ($(COMPILER),gcc)
RISCV_CCFLAGS            += $(RISCV_FLAGS_GCC) $(RISCV_FLAGS_COMMON)
RISCV_CXXFLAGS           += $(RISCV_CCFLAGS)
RISCV_LDFLAGS            += -static -nostartfiles -lm -lgcc $(RISCV_FLAGS_GCC) $(RISCV_FLAGS_COMMON) -L$(ROOT_DIR)
RISCV_OBJDUMP_FLAGS      += $(RISCV_OBJDUMP_FLAGS_GCC)
RISCV_CCFLAGS_TESTS      ?= $(RISCV_FLAGS_GCC) $(RISCV_FLAGS_COMMON_TESTS) -fvisibility=hidden -nostdlib $(RISCV_LDFLAGS)
# LLVM Flags
else
RISCV_CCFLAGS            += $(RISCV_LLVM_TARGET) $(RISCV_FLAGS_LLVM) $(RISCV_FLAGS_COMMON)
RISCV_CXXFLAGS           += $(RISCV_CCFLAGS)
RISCV_LDFLAGS            += -static -nostartfiles -lm -lgcc -mcmodel=small $(RISCV_LLVM_TARGET) $(RISCV_FLAGS_COMMON) -L$(ROOT_DIR)
RISCV_OBJDUMP_FLAGS      += $(RISCV_OBJDUMP_FLAGS_LLVM)
RISCV_CCFLAGS_TESTS      ?= $(RISCV_FLAGS_LLVM_TESTS) $(RISCV_FLAGS_COMMON_TESTS) -fvisibility=hidden -nostdlib $(RISCV_LDFLAGS)
endif

ifeq ($(MULTI_CLUSTER),true)
LINKER_SCRIPT     ?= $(MULTI_CLUSTER_DIR)/mc_memory.ld
LINKER_SCRIPT_DEP ?= $(ROOT_DIR)/arch.ld
RUNTIME += $(MULTI_CLUSTER_DIR)/mc_start.S.o
RUNTIME += $(ROOT_DIR)/string.c.o
RUNTIME += $(ROOT_DIR)/synchronization.c.o
else
LINKER_SCRIPT     ?= $(ROOT_DIR)/arch.ld
LINKER_SCRIPT_DEP ?=
RUNTIME += $(ROOT_DIR)/alloc.c.o
RUNTIME += $(ROOT_DIR)/crt0.S.o
RUNTIME += $(ROOT_DIR)/printf.c.o
RUNTIME += $(ROOT_DIR)/serial.c.o
RUNTIME += $(ROOT_DIR)/string.c.o
RUNTIME += $(ROOT_DIR)/synchronization.c.o
endif

OMP_RUNTIME := $(addsuffix .o,$(shell find $(OMP_DIR) -name "*.c"))
HALIDE_RUNTIME := $(addsuffix .o,$(shell find $(HALIDE_DIR) -name "*.c"))

.INTERMEDIATE: $(RUNTIME) $(OMP_RUNTIME) $(HALIDE_RUNTIME) $(LINKER_SCRIPT)
# Disable builtin rules
.SUFFIXES:

# Generate the FlexCluster architecture headers from the selected config.
ifeq ($(MULTI_CLUSTER),true)
$(MC_ARCH_HDR) $(MC_ARCH_INC) &: $(MC_ARCH_CONFIG) $(MULTI_CLUSTER_DIR)/gen_mc_arch.py FORCE
	$(python) $(MULTI_CLUSTER_DIR)/gen_mc_arch.py $(MC_ARCH_CONFIG) --outdir $(MULTI_CLUSTER_DIR)/include
endif

%.S.o: %.S $(MC_HDR_DEP)
	$(RISCV_CC) $(RISCV_CCFLAGS) -c $< -o $@

%.c.o: %.c $(MC_HDR_DEP)
	$(RISCV_CC) $(RISCV_CCFLAGS) -c $< -o $@

%.cpp.o: %.cpp $(MC_HDR_DEP)
	$(RISCV_CXX) $(RISCV_CXXFLAGS) -c $< -o $@

%.ld: %.ld.c FORCE
	$(RISCV_CC) -P -E $(DEFINES) $< -o $@

data_%.h: $(DATA_DIR)/gendata_params.hjson
	$(python) $(DATA_DIR)/gendata_header.py --app_name $* --params $(DATA_DIR)/gendata_params.hjson

.PHONY: FORCE
FORCE:

# Bootrom
%.elf: %.S $(ROOT_DIR)/bootrom.ld $(LINKER_SCRIPT)
	$(RISCV_CC) $(RISCV_CCFLAGS) -L$(ROOT_DIR) -T$(ROOT_DIR)/bootrom.ld $< -nostdlib -static -Wl,--no-gc-sections -o $@

%.bin: %.elf
	$(RISCV_OBJCOPY) -O binary $< $@

%.img: %.bin
	dd if=$< of=$@ bs=128

# Convenience formatting
format:
	make -C $(MEMPOOL_DIR) format
