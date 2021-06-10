# Copyright 2021 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Author: Matheus Cavalcante, ETH Zurich
#         Samuel Riedel, ETH Zurich

SHELL = /usr/bin/env bash
ROOT_DIR := $(patsubst %/,%, $(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
MEMPOOL_DIR := $(shell git rev-parse --show-toplevel 2>/dev/null || echo $$MEMPOOL_DIR)

# Include configuration
config_mk = $(abspath $(ROOT_DIR)/config/config.mk)
include $(config_mk)

INSTALL_PREFIX        ?= install
APPS_PREFIX           ?= apps
INSTALL_DIR           ?= ${ROOT_DIR}/${INSTALL_PREFIX}
GCC_INSTALL_DIR       ?= ${INSTALL_DIR}/riscv-gcc
ISA_SIM_INSTALL_DIR   ?= ${INSTALL_DIR}/riscv-isa-sim
LLVM_INSTALL_DIR      ?= ${INSTALL_DIR}/llvm
HALIDE_INSTALL_DIR    ?= ${INSTALL_DIR}/halide
BENDER_INSTALL_DIR    ?= ${INSTALL_DIR}/bender
VERILATOR_INSTALL_DIR ?= ${INSTALL_DIR}/verilator
RISCV_TESTS_DIR       ?= ${ROOT_DIR}/${APPS_PREFIX}/riscv-tests

CMAKE ?= cmake
# CC and CXX are Makefile default variables that are always defined in a Makefile. Hence, overwrite
# the variable if it is only defined by the Makefile (its origin in the Makefile's default).
ifeq ($(origin CC),default)
CC  = gcc
endif
ifeq ($(origin CXX),default)
CXX = g++
endif
BENDER_VERSION = 0.21.0

# Default target
all: toolchain riscv-isa-sim halide

# Halide
halide:
	mkdir -p $(HALIDE_INSTALL_DIR)
	cd toolchain/halide && mkdir -p build && cd build; \
	$(CMAKE) \
		-DLLVM_DIR=$(LLVM_INSTALL_DIR)/lib/cmake/llvm \
		-DCMAKE_INSTALL_PREFIX=$(HALIDE_INSTALL_DIR) \
		-DCMAKE_CXX_COMPILER=$(CXX) \
		-DCMAKE_C_COMPILER=$(CC) \
		-DCMAKE_BUILD_TYPE=Release \
		.. && \
	make -j4 all && \
	make install

# Toolchain
toolchain: tc-riscv-gcc tc-llvm

tc-riscv-gcc:
	mkdir -p $(GCC_INSTALL_DIR)
	cd $(CURDIR)/toolchain/riscv-gnu-toolchain && rm -rf build && mkdir -p build && cd build && \
	../configure --prefix=$(GCC_INSTALL_DIR) --with-arch=rv32im --with-cmodel=medlow --enable-multilib && \
	$(MAKE) MAKEINFO=true -j4

tc-llvm:
	mkdir -p $(LLVM_INSTALL_DIR)
	cd $(CURDIR)/toolchain/llvm-project && mkdir -p build && cd build; \
	$(CMAKE) \
		-DCMAKE_INSTALL_PREFIX=$(LLVM_INSTALL_DIR) \
		-DCMAKE_CXX_COMPILER=$(CXX) \
		-DCMAKE_C_COMPILER=$(CC) \
		-DLLVM_ENABLE_PROJECTS="clang" \
		-DLLVM_TARGETS_TO_BUILD="RISCV;host" \
		-DLLVM_BUILD_DOCS="0" \
		-DLLVM_ENABLE_TERMINFO="0"  \
		-DLLVM_ENABLE_ASSERTIONS=ON \
		-DCMAKE_BUILD_TYPE=Release \
		../llvm && \
	make -j4 all && \
	make install

riscv-isa-sim: update_opcodes
	cd toolchain/riscv-isa-sim && mkdir -p build && cd build; \
	[ -d dtc ] || git clone git://git.kernel.org/pub/scm/utils/dtc/dtc.git && cd dtc; \
	make install SETUP_PREFIX=$(ISA_SIM_INSTALL_DIR) PREFIX=$(ISA_SIM_INSTALL_DIR) && \
	PATH=$(ISA_SIM_INSTALL_DIR)/bin:$$PATH; cd ..; \
	../configure --prefix=$(ISA_SIM_INSTALL_DIR) && make && make install

# Unit tests for verification
MINPOOL_CONFIG = num_cores=16 num_cores_per_tile=4

.PHONY: test build_test clean_test

test: build_test
	export PATH=$(ISA_SIM_INSTALL_DIR)/bin:$$PATH; \
	make -C $(RISCV_TESTS_DIR)/isa run && \
	COMPILER=gcc $(MINPOOL_CONFIG) make -C $(APPS_PREFIX) test && \
	$(MINPOOL_CONFIG) make -C hardware simc_test

build_test: update_opcodes
	cd $(RISCV_TESTS_DIR); \
	autoconf && ./configure --with-xlen=32 --prefix=$$(pwd)/target && \
	make isa -j4 && make install && \
	cd isa && make -j4 all && \
	$(MINPOOL_CONFIG) make -C ../../../hardware compile

clean_test:
	$(MAKE) -C hardware clean
	$(MAKE) -C $(APPS_PREFIX) clean
	$(MAKE) -C $(RISCV_TESTS_DIR) clean

# Bender
bender: check-bender
check-bender:
	@if [ -x $(BENDER_INSTALL_DIR)/bender ]; then \
		req="bender $(BENDER_VERSION)"; \
		current="$$($(BENDER_INSTALL_DIR)/bender --version)"; \
		if [ "$$(printf '%s\n' "$${req}" "$${current}" | sort -V | head -n1)" != "$${req}" ]; then \
			rm -rf $(BENDER_INSTALL_DIR); \
		fi \
	fi
	@$(MAKE) -C $(ROOT_DIR) $(BENDER_INSTALL_DIR)/bender

$(BENDER_INSTALL_DIR)/bender:
	mkdir -p $(BENDER_INSTALL_DIR) && cd $(BENDER_INSTALL_DIR) && \
	curl --proto '=https' --tlsv1.2 https://pulp-platform.github.io/bender/init -sSf | sh

# Verilator
verilator: $(VERILATOR_INSTALL_DIR)/bin/verilator
$(VERILATOR_INSTALL_DIR)/bin/verilator: toolchain/verilator Makefile
	cd $<; unset VERILATOR_ROOT; \
	autoconf && ./configure --prefix=$(VERILATOR_INSTALL_DIR) $(VERILATOR_CI) && \
	make -j4 && make install

# Helper targets
.PHONY: clean format apps

apps:
	make -C apps

update_opcodes:
	make -C toolchain/riscv-opcodes all

format:
	$(LLVM_INSTALL_DIR)/bin/clang-format -style=file -i --verbose $$(git diff --name-only HEAD | tr ' ' '\n' | grep -P "(?<!\.ld)\.(h|c|cpp)\b")

clean: clean_test
	rm -rf $(INSTALL_DIR)
