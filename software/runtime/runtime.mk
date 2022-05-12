# Copyright 2021 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Author: Samuel Riedel, ETH Zurich
#         Matheus Cavalcante, ETH Zurich
SHELL = /usr/bin/env bash

ROOT_DIR := $(patsubst %/,%, $(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
MEMPOOL_DIR := $(shell git rev-parse --show-toplevel 2>/dev/null || echo $$MEMPOOL_DIR)
# Include configuration
include $(MEMPOOL_DIR)/config/config.mk

INSTALL_DIR        ?= $(MEMPOOL_DIR)/install
GCC_INSTALL_DIR    ?= $(INSTALL_DIR)/riscv-gcc
LLVM_INSTALL_DIR   ?= $(INSTALL_DIR)/llvm
HALIDE_INSTALL_DIR ?= $(INSTALL_DIR)/halide
HALIDE_INCLUDE     ?= $(HALIDE_INSTALL_DIR)/include
HALIDE_LIB         ?= $(HALIDE_INSTALL_DIR)/lib

COMPILER      ?= gcc
XPULPIMG      ?= $(xpulpimg)

RISCV_XLEN    ?= 32

RISCV_ABI     ?= ilp32
RISCV_TARGET  ?= riscv$(RISCV_XLEN)-unknown-elf
ifeq ($(COMPILER),gcc)
	# Use GCC
	# GCC compiler -march
	ifeq ($(XPULPIMG),1)
		RISCV_ARCH    ?= rv$(RISCV_XLEN)imaXpulpimg
		RISCV_ARCH_AS ?= $(RISCV_ARCH)
		# Define __XPULPIMG if the extension is active
		DEFINES       += -D__XPULPIMG
	else
		RISCV_ARCH    ?= rv$(RISCV_XLEN)ima
		RISCV_ARCH_AS ?= $(RISCV_ARCH)Xpulpv2
	endif
	# GCC Toolchain
	RISCV_PREFIX  ?= $(GCC_INSTALL_DIR)/bin/$(RISCV_TARGET)-
	RISCV_CC      ?= $(RISCV_PREFIX)gcc
	RISCV_CXX     ?= $(RISCV_PREFIX)g++
	RISCV_OBJDUMP ?= $(RISCV_PREFIX)objdump
else
	# Use LLVM by default
	# LLVM compiler -march
	RISCV_ARCH    ?= rv$(RISCV_XLEN)ima
	# GCC Toolchain
	RISCV_PREFIX  ?= $(LLVM_INSTALL_DIR)/bin/llvm-
	RISCV_CC      ?= $(LLVM_INSTALL_DIR)/bin/clang
	RISCV_CXX     ?= $(LLVM_INSTALL_DIR)/bin/clang++
	RISCV_OBJDUMP ?= $(GCC_INSTALL_DIR)/bin/$(RISCV_TARGET)-objdump
endif
RISCV_OBJCOPY ?= $(RISCV_PREFIX)objcopy
RISCV_AS      ?= $(RISCV_PREFIX)as
RISCV_AR      ?= $(RISCV_PREFIX)ar
RISCV_LD      ?= $(RISCV_PREFIX)ld
RISCV_STRIP   ?= $(RISCV_PREFIX)strip

# Defines
DEFINES += -DPRINTF_DISABLE_SUPPORT_FLOAT -DPRINTF_DISABLE_SUPPORT_LONG_LONG -DPRINTF_DISABLE_SUPPORT_PTRDIFF_T
DEFINES += -DNUM_CORES=$(num_cores)
DEFINES += -DNUM_GROUPS=$(num_groups)
DEFINES += -DNUM_CORES_PER_TILE=$(num_cores_per_tile)
DEFINES += -DNUM_CORES_PER_GROUP=$(shell awk 'BEGIN{print $(num_cores)/$(num_groups)}')
DEFINES += -DNUM_TILES_PER_GROUP=$(shell awk 'BEGIN{print $(num_cores_per_group)/$(num_cores_per_tile)}')
DEFINES += -DLOG2_NUM_CORES_PER_TILE=$(shell awk 'BEGIN{print log($(num_cores_per_tile))/log(2)}')
DEFINES += -DBOOT_ADDR=0x$(boot_addr)
DEFINES += -DL2_BASE=0x$(l2_base)
DEFINES += -DL2_SIZE=0x$(l2_size)
DEFINES += -DSEQ_MEM_SIZE=$(seq_mem_size)
DEFINES += -DLOG2_SEQ_MEM_SIZE=$(shell awk 'BEGIN{print log($(seq_mem_size))/log(2)}')
DEFINES += -DSTACK_SIZE=$(stack_size)
DEFINES += -DLOG2_STACK_SIZE=$(shell awk 'BEGIN{print log($(stack_size))/log(2)}')
DEFINES += -DXQUEUE_SIZE=$(xqueue_size)

# Specify cross compilation target. This can be omitted if LLVM is built with riscv as default target
RISCV_LLVM_TARGET  ?= --target=$(RISCV_TARGET) --sysroot=$(GCC_INSTALL_DIR)/$(RISCV_TARGET) --gcc-toolchain=$(GCC_INSTALL_DIR)

RISCV_WARNINGS += -Wunused-variable -Wconversion -Wall -Wextra # -Werror
RISCV_FLAGS_COMMON_TESTS ?= -march=$(RISCV_ARCH) -mabi=$(RISCV_ABI) -I$(ROOT_DIR) -I$(HALIDE_INCLUDE) -static
RISCV_FLAGS_COMMON ?= $(RISCV_FLAGS_COMMON_TESTS) -g -std=gnu99 -O3 -ffast-math -fno-common -fno-builtin-printf $(DEFINES) $(RISCV_WARNINGS)
RISCV_FLAGS_GCC    ?= -mcmodel=medany -Wa,-march=$(RISCV_ARCH_AS) -mtune=mempool # -falign-loops=32 -falign-jumps=32
RISCV_FLAGS_LLVM   ?= -mcmodel=small -mcpu=mempool-rv32 -mllvm -misched-topdown

ifeq ($(COMPILER),gcc)
	RISCV_CCFLAGS       ?= $(RISCV_FLAGS_GCC) $(RISCV_FLAGS_COMMON)
	RISCV_CXXFLAGS      ?= $(RISCV_CCFLAGS)
	RISCV_LDFLAGS       ?= -static -nostartfiles -lm -lgcc $(RISCV_CCFLAGS) -L$(ROOT_DIR)
	RISCV_OBJDUMP_FLAGS ?= --disassembler-option="march=$(RISCV_ARCH_AS)"
else
	RISCV_CCFLAGS       ?= $(RISCV_LLVM_TARGET) $(RISCV_FLAGS_LLVM) $(RISCV_FLAGS_COMMON)
	RISCV_CXXFLAGS      ?= $(RISCV_CCFLAGS)
	RISCV_LDFLAGS       ?= -static -nostartfiles -lm -lgcc -mcmodel=small $(RISCV_LLVM_TARGET) $(RISCV_FLAGS_COMMON) -L$(ROOT_DIR)
	RISCV_OBJDUMP_FLAGS ?=
endif

LINKER_SCRIPT ?= $(ROOT_DIR)/arch.ld
RUNTIME ?= $(ROOT_DIR)/crt0.S.o $(ROOT_DIR)/printf.c.o $(ROOT_DIR)/string.c.o $(ROOT_DIR)/synchronization.c.o $(ROOT_DIR)/serial.c.o $(ROOT_DIR)/alloc.c.o

# For unit tests
RISCV_CCFLAGS_TESTS ?= $(RISCV_FLAGS_GCC) $(RISCV_FLAGS_COMMON_TESTS) -fvisibility=hidden -nostdlib $(RISCV_LDFLAGS)

.INTERMEDIATE: $(RUNTIME) $(LINKER_SCRIPT)
# Disable builtin rules
.SUFFIXES:

%.S.o: %.S
	$(RISCV_CC) $(RISCV_CCFLAGS) -c $< -o $@

%.c.o: %.c
	$(RISCV_CC) $(RISCV_CCFLAGS) -c $< -o $@

%.cpp.o: %.cpp
	$(RISCV_CXX) $(RISCV_CXXFLAGS) -c $< -o $@

%.ld: %.ld.c
	$(RISCV_CC) -P -E $(DEFINES) $< -o $@

# Bootrom
%.elf: %.S $(ROOT_DIR)/bootrom.ld $(LINKER_SCRIPT)
	$(RISCV_CC) $(RISCV_CCFLAGS) -L$(ROOT_DIR) -T$(ROOT_DIR)/bootrom.ld $< -nostdlib -static -Wl,--no-gc-sections -o $@

%.bin: %.elf
	$(RISCV_OBJCOPY) -O binary $< $@

%.img: %.bin
	dd if=$< of=$@ bs=128
