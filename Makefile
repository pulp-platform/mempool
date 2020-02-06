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

ROOT_DIR := $(patsubst %/,%, $(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
SHELL = bash

INSTALL_PREFIX     ?= install
INSTALL_DIR        ?= ${ROOT_DIR}/${INSTALL_PREFIX}
GCC_INSTALL_DIR    ?= ${INSTALL_DIR}/riscv-gcc
LLVM_INSTALL_DIR   ?= ${INSTALL_DIR}/llvm
HALIDE_INSTALL_DIR ?= ${INSTALL_DIR}/halide

CMAKE ?= cmake-3.7.1
CC    ?= gcc-8.2.0
CXX   ?= g++-8.2.0

# Halide
halide: toolchain
	mkdir -p $(HALIDE_INSTALL_DIR)
	cd toolchain/halide && mkdir -p build && cd build; \
	$(CMAKE) \
		-DLLVM_DIR=$(LLVM_INSTALL_DIR)/lib/cmake/llvm \
		-DCMAKE_INSTALL_PREFIX=$(INSTALL_DIR)/halide \
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
	cd $(CURDIR)/toolchain/riscv-gnu-toolchain && git submodule update --init --recursive && ./configure --prefix=$(GCC_INSTALL_DIR)/riscv-gcc --with-arch=rv32im --with-cmodel=medlow --enable-multilib && $(MAKE) -j4

tc-llvm:
	mkdir -p $(LLVM_INSTALL_DIR)
	cd $(CURDIR)/toolchain/llvm-project && mkdir -p build && cd build; \
	$(CMAKE) \
		-DCMAKE_INSTALL_PREFIX=$(LLVM_INSTALL_DIR) \
		-DCMAKE_CXX_COMPILER=$(CXX) \
		-DCMAKE_C_COMPILER=$(CC) \
		-DLLVM_ENABLE_PROJECTS="clang" \
		-DLLVM_TARGETS_TO_BUILD="RISCV;host" \
		-DLLVM_BUILD_DOCS="1" \
		-DLLVM_ENABLE_TERMINFO="0"  \
		-DLLVM_ENABLE_ASSERTIONS=ON \
		-DCMAKE_BUILD_TYPE=Release \
		../llvm && \
	make -j4 all && \
	make install

# Helper targets
.PHONY: clean

clean:
	rm -rf $(INSTALL_DIR)
