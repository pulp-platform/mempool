# Copyright 2020 ETH Zurich and University of Bologna.
#
# SPDX-License-Identifier: Apache-2.0
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#    http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

# Author: Samuel Riedel, ETH Zurich
#         Matheus Cavalcante, ETH Zurich

INSTALL_DIR        ?= ../install
GCC_INSTALL_DIR    ?= $(INSTALL_DIR)/riscv-gcc
LLVM_INSTALL_DIR   ?= $(INSTALL_DIR)/llvm
HALIDE_INSTALL_DIR ?= $(INSTALL_DIR)/halide

COMPILER      ?= llvm

RISCV_XLEN    ?= 32
RISCV_ARCH    ?= rv$(RISCV_XLEN)ima
RISCV_ABI     ?= ilp32
RISCV_TARGET  ?= riscv$(RISCV_XLEN)-unknown-elf
ifeq ($(COMPILER),gcc)
	# Use GCC
	RISCV_PREFIX  ?= $(GCC_INSTALL_DIR)/bin/$(RISCV_TARGET)-
	RISCV_CC      ?= $(RISCV_PREFIX)gcc
	RISCV_CXX     ?= $(RISCV_PREFIX)g++
else
	# Use LLVM by default
	RISCV_PREFIX  ?= $(LLVM_INSTALL_DIR)/bin/llvm-
	RISCV_CC      ?= $(LLVM_INSTALL_DIR)/bin/clang
	RISCV_CXX     ?= $(LLVM_INSTALL_DIR)/bin/clang++
endif
RISCV_OBJDUMP ?= $(RISCV_PREFIX)objdump
RISCV_OBJCOPY ?= $(RISCV_PREFIX)objcopy
RISCV_AS      ?= $(RISCV_PREFIX)as
RISCV_AR      ?= $(RISCV_PREFIX)ar
RISCV_LD      ?= $(RISCV_PREFIX)ld
RISCV_STRIP   ?= $(RISCV_PREFIX)strip

# Specify cross compilation target. This can be omitted if LLVM is built with riscv as default target
RISCV_LLVM_TARGET  ?= --target=$(RISCV_TARGET) --sysroot=$(GCC_INSTALL_DIR)/$(RISCV_TARGET) --gcc-toolchain=$(GCC_INSTALL_DIR)

RISCV_FLAGS_COMMON ?= -march=$(RISCV_ARCH) -mabi=$(RISCV_ABI) -I$(CURDIR)/common -static -std=gnu99 -O3 -ffast-math -fno-common -fno-builtin-printf
RISCV_FLAGS_GCC    ?= -mcmodel=medany
RISCV_FLAGS_LLVM   ?= -mcmodel=small
ifeq ($(COMPILER),gcc)
	RISCV_FLAGS    ?= $(RISCV_FLAGS_GCC)  $(RISCV_FLAGS_COMMON)
else
	RISCV_FLAGS    ?= $(RISCV_LLVM_TARGET) $(RISCV_FLAGS_LLVM) $(RISCV_FLAGS_COMMON)
endif

RISCV_CCFLAGS  ?= $(RISCV_FLAGS)
RISCV_CXXFLAGS ?= $(RISCV_FLAGS)
RISCV_LDFLAGS  ?= -static -nostartfiles -lm -lgcc $(RISCV_FLAGS)

RUNTIME ?= common/crt0.S.o common/printf.c.o common/string.c.o common/serial.c.o common/arch.ld
HDR ?=     common/runtime.h

%.S.o: %.S
	$(RISCV_CC) $(RISCV_CCFLAGS) -c $< -o $@

%.c.o: %.c
	$(RISCV_CC) $(RISCV_CCFLAGS) -c $< -o $@

%.cpp.o: %.cpp
	$(RISCV_CXX) $(RISCV_CXXFLAGS) -c $< -o $@
