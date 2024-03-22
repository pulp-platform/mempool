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
SOFTWARE_DIR          ?= software
INSTALL_DIR           ?= ${ROOT_DIR}/${INSTALL_PREFIX}
GCC_INSTALL_DIR       ?= ${INSTALL_DIR}/riscv-gcc
ISA_SIM_INSTALL_DIR   ?= ${INSTALL_DIR}/riscv-isa-sim
LLVM_INSTALL_DIR      ?= ${INSTALL_DIR}/llvm
HALIDE_INSTALL_DIR    ?= ${INSTALL_DIR}/halide
BENDER_INSTALL_DIR    ?= ${INSTALL_DIR}/bender
VERILATOR_INSTALL_DIR ?= ${INSTALL_DIR}/verilator
RISCV_TESTS_DIR       ?= ${ROOT_DIR}/${SOFTWARE_DIR}/riscv-tests

CMAKE ?= cmake-3.28.3
# CC and CXX are Makefile default variables that are always defined in a Makefile. Hence, overwrite
# the variable if it is only defined by the Makefile (its origin in the Makefile's default).
ifeq ($(origin CC),default)
  CC  = gcc
endif
ifeq ($(origin CXX),default)
  CXX = g++
endif
BENDER_VERSION = 0.28.1

# We need a recent LLVM installation (>11) to compile Verilator.
# We also need to link the binaries with LLVM's libc++.
# Define CLANG_PATH to be the path of your Clang installation.
# At IIS, check .gitlab/.gitlab-ci.yml for an example CLANG_PATH.

ifneq (${CLANG_PATH},)
  CLANG_CC       := $(CLANG_PATH)/bin/clang
  CLANG_CXX      := $(CLANG_PATH)/bin/clang++
  CLANG_CXXFLAGS := "-nostdinc++ -isystem $(CLANG_PATH)/include/c++/v1"
  CLANG_LDFLAGS  := "-L $(CLANG_PATH)/lib -Wl,-rpath,$(CLANG_PATH)/lib -lc++ -nostdlib++"
else
  CLANG_CC       ?= clang
  CLANG_CXX      ?= clang++
  CLANG_CXXFLAGS := ""
  CLANG_LDFLAGS  := ""
endif

# Default target
all: toolchain riscv-isa-sim halide

# Halide
halide:
	mkdir -p $(HALIDE_INSTALL_DIR)
	cd toolchain/halide && mkdir -p build && cd build; \
	$(CMAKE) \
		-DLLVM_DIR=$(LLVM_INSTALL_DIR)/lib/cmake/llvm \
		-DCMAKE_INSTALL_PREFIX=$(HALIDE_INSTALL_DIR) \
		-DCMAKE_INSTALL_LIBDIR=lib \
		-DCMAKE_CXX_COMPILER=$(CXX) \
		-DCMAKE_C_COMPILER=$(CC) \
		-DWITH_PYTHON_BINDINGS=OFF \
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
	$(MAKE) MAKEINFO=true -j4 && \
	cp ../riscv.ld $(GCC_INSTALL_DIR)/riscv32-unknown-elf/lib

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
		-DLLVM_ENABLE_BINDINGS="0" \
		-DLLVM_ENABLE_TERMINFO="0"  \
		-DLLVM_OPTIMIZED_TABLEGEN=ON \
		-DCMAKE_BUILD_TYPE=Release \
		../llvm && \
	make -j4 all && \
	make install

riscv-isa-sim: update_opcodes
	cd toolchain/riscv-isa-sim && mkdir -p build && cd build; \
	../configure --prefix=$(ISA_SIM_INSTALL_DIR) && make && make install

# Unit tests for verification
.PHONY: riscv-tests build-riscv-tests clean-riscv-tests

riscv-tests: build-riscv-tests
	export PATH=$(ISA_SIM_INSTALL_DIR)/bin:$$PATH; \
	make -C $(RISCV_TESTS_DIR)/isa run && \
	config=minpool COMPILER=gcc make -C $(SOFTWARE_DIR) riscv-tests && \
	config=minpool make -C hardware verilate_test

build-riscv-tests: update_opcodes
	cd $(RISCV_TESTS_DIR); \
	autoconf && ./configure --with-xlen=32 --prefix=$$(pwd)/target && \
	make isa -j4 && make install && \
	cd isa && make -j4 all

clean-riscv-tests:
	$(MAKE) -C hardware clean
	$(MAKE) -C $(SOFTWARE_DIR) clean
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
	curl --proto '=https' --tlsv1.2 https://pulp-platform.github.io/bender/init -sSf | sh -s -- $(BENDER_VERSION)

# Verilator
verilator: $(VERILATOR_INSTALL_DIR)/bin/verilator
$(VERILATOR_INSTALL_DIR)/bin/verilator: toolchain/verilator Makefile
	cd $<; unset VERILATOR_ROOT; \
	autoconf && CC=$(CLANG_CC) CXX=$(CLANG_CXX) CXXFLAGS=$(CLANG_CXXFLAGS) LDFLAGS=$(CLANG_LDFLAGS) ./configure --prefix=$(VERILATOR_INSTALL_DIR) $(VERILATOR_CI) && \
	make -j4 && make install

# Update and patch hardware dependencies for MemPool
# Previous changes will be stashed. Clear all the stashes with `git stash clear`
.PHONY: update-deps
update-deps:
	for dep in $(shell git config --file .gitmodules --get-regexp path \
	| awk '/hardware/{ print $$2 }'); do \
	  git -C $${dep} diff --quiet || { echo $${dep}; git -C $${dep} stash -u; }; \
	  git submodule update --init --recursive -- $${dep}; \
	done
	git apply hardware/deps/patches/*

# Build, update and patch the DRAMsys submodule
$(eval DRAM_PATH=$(realpath $(shell git config --file .gitmodules --get-regexp dram_rtl_sim.path | awk '/hardware/{ print $$2 }')))
$(eval DRAM_LIB_PATH=$(DRAM_PATH)/dramsys_lib)
$(eval DRAMSYS_PATH=$(DRAM_LIB_PATH)/DRAMSys)
$(eval DRAMSYS_PATCH_PATH=$(DRAM_LIB_PATH)/dramsys_lib_patch)
$(eval DRAMSYS_SO_PATH=$(DRAMSYS_PATH)/build)

clean-dram:
	if [ -d "$(DRAMSYS_PATH)" ]; then \
		rm -rf $(DRAMSYS_PATH); \
	fi

build-dram: clean-dram
	if [ ! -d "$(DRAMSYS_PATH)" ]; then \
		git clone https://github.com/tukl-msd/DRAMSys.git $(DRAMSYS_PATH); \
	fi
	cd $(DRAMSYS_PATH) && git reset --hard 8e021ea && git apply $(DRAMSYS_PATCH_PATH)

config-dram: build-dram
	@cp hardware/include/dram_config/am_hbm2e_16Gb_pc_brc.json $(DRAMSYS_PATH)/configs/addressmapping/.
	@cp hardware/include/dram_config/mc_hbm2e_fr_fcfs_grp.json $(DRAMSYS_PATH)/configs/mcconfig/.
	@cp hardware/include/dram_config/ms_hbm2e_16Gb_3600.json $(DRAMSYS_PATH)/configs/memspec/.
	@cp hardware/include/dram_config/simconfig_hbm2e.json $(DRAMSYS_PATH)/configs/simconfig/.
	@mv $(DRAMSYS_PATH)/configs/hbm2-example.json $(DRAMSYS_PATH)/configs/hbm2-example.json.ori
	@cp hardware/include/dram_config/HBM2E-3600.json $(DRAMSYS_PATH)/configs/hbm2-example.json

setup-dram: config-dram
	cd $(DRAMSYS_PATH) && \
	if [ ! -d "build" ]; then \
		mkdir build && cd build; \
		CC=gcc-11.2.0 CXX=g++-11.2.0 cmake -DCMAKE_CXX_FLAGS=-fPIC -DCMAKE_C_FLAGS=-fPIC -D DRAMSYS_WITH_DRAMPOWER=ON .. ; \
		make -j; \
	fi

# Helper targets
.PHONY: clean format apps

apps:
	make -C $(SOFTWARE_DIR) apps

update_opcodes: software/runtime/encoding.h hardware/deps/snitch/src/riscv_instr.sv

software/runtime/encoding.h: toolchain/riscv-opcodes/*
	make -C toolchain/riscv-opcodes encoding_out.h
	mv toolchain/riscv-opcodes/encoding_out.h $@
	ln -fsr $@ toolchain/riscv-isa-sim/riscv/encoding.h
	ln -fsr $@ software/riscv-tests/env/encoding.h #this will change when riscv-tests is a submodule

hardware/deps/snitch/src/riscv_instr.sv: toolchain/riscv-opcodes/*
	make -C toolchain/riscv-opcodes inst.sverilog
	mv toolchain/riscv-opcodes/inst.sverilog $@

toolchain/riscv-opcodes/*:
	git submodule update --init --recursive -- toolchain/riscv-opcodes

format:
	$(ROOT_DIR)/scripts/run_clang_format.py --clang-format-executable=$(LLVM_INSTALL_DIR)/bin/clang-format -i -r $(ROOT_DIR)

clean: clean_test
	rm -rf $(INSTALL_DIR)
