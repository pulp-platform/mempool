# Copyright 2019 ETH Zurich and University of Bologna.
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

# Author: Matheus Cavalcante, ETH Zurich
#         Samuel Riedel, ETH Zurich

SHELL = /usr/bin/env bash
ROOT_DIR := $(patsubst %/,%, $(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
MEMPOOL_DIR := $(shell git rev-parse --show-toplevel 2>/dev/null || echo $$MEMPOOL_DIR)

INSTALL_PREFIX      ?= install
INSTALL_DIR         ?= ${ROOT_DIR}/${INSTALL_PREFIX}
GCC_INSTALL_DIR     ?= ${INSTALL_DIR}/riscv-gcc
ISA_SIM_INSTALL_DIR ?= ${INSTALL_DIR}/riscv-isa-sim
LLVM_INSTALL_DIR    ?= ${INSTALL_DIR}/llvm
HALIDE_INSTALL_DIR  ?= ${INSTALL_DIR}/halide

CMAKE ?= cmake-3.18.1
# CC and CXX are Makefile default variables that are always defined in a Makefile. Hence, overwrite
# the variable if it is only defined by the Makefile (its origin in the Makefile's default).
ifeq ($(origin CC),default)
CC     = gcc-8.2.0
endif
ifeq ($(origin CXX),default)
CXX    = g++-8.2.0
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

riscv-isa-sim:
	cd toolchain/riscv-isa-sim && mkdir -p build && cd build; \
	[ -d dtc ] || git clone git://git.kernel.org/pub/scm/utils/dtc/dtc.git && cd dtc; \
	make install SETUP_PREFIX=$$(pwd)/install PREFIX=$$(pwd)/install && \
	PATH=$$(pwd)/install/bin:$$PATH; cd ..; \
	../configure --prefix=$(ISA_SIM_INSTALL_DIR) && make && make install

# Helper targets
.PHONY: clean format apps

apps:
	make -C apps

format:
	$(LLVM_INSTALL_DIR)/bin/clang-format -style=file -i --verbose $$(git diff --name-only HEAD | tr ' ' '\n' | grep -E "\.(h|c|cpp)\b")

clean:
	rm -rf $(INSTALL_DIR)
