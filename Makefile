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

ROOT_DIR := $(patsubst %/,%, $(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
SHELL = bash

INSTALL_PREFIX     ?= install
INSTALL_DIR        ?= ${ROOT_DIR}/${INSTALL_PREFIX}
LLVM_INSTALL_DIR   ?= ${INSTALL_DIR}/llvm
HALIDE_INSTALL_DIR ?= ${INSTALL_DIR}/halide
GCC_INSTALL_DIR    ?= ${INSTALL_DIR}/riscv-gcc

CMAKE ?= cmake
CC    ?= gcc
CXX   ?= g++

toolchain: config llvm halide riscv-gcc pulp-sdk

config:
	@echo "INSTALL_DIR        $(INSTALL_DIR)"
	@echo "LLVM_INSTALL_DIR   $(LLVM_INSTALL_DIR)"
	@echo "HALIDE_INSTALL_DIR $(HALIDE_INSTALL_DIR)"
	@echo "GCC_INSTALL_DIR    $(GCC_INSTALL_DIR)"
	@echo "LLVM_CONFIG        $(LLVM_CONFIG)"
	@echo "CMAKE              $(CMAKE)"
	@echo "CC                 $(CC)"
	@echo "CXX                $(CXX)"

llvm:
	@echo Configuration: cmake=$(CMAKE), CC=$(CC), CXX=$(CXX)
	mkdir -p $(LLVM_INSTALL_DIR)
	cd toolchain/llvm-project && mkdir -p build && cd build; pwd; \
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
	make -j7 all && \
	make install

halide:
	@echo Configuration: cmake=$(CMAKE), CC=$(CC), CXX=$(CXX)
	mkdir -p $(HALIDE_INSTALL_DIR)
	cd toolchain/Halide && mkdir -p build && cd build; \
	$(CMAKE) \
		-DLLVM_DIR=$(LLVM_INSTALL_DIR)/lib/cmake/llvm \
		-DCMAKE_INSTALL_PREFIX=$(HALIDE_INSTALL_DIR) \
		-DCMAKE_CXX_COMPILER=$(CXX) \
		-DCMAKE_C_COMPILER=$(CC) \
		-DCMAKE_BUILD_TYPE=Release \
		.. && \
	make -j7 all && \
	make install

riscv-gcc:
	mkdir -p $(GCC_INSTALL_DIR)
	cd toolchain/pulp-riscv-gnu-toolchain && \
	git submodule update --init --recursive && \
	./configure --prefix=$(GCC_INSTALL_DIR) --with-arch=rv32imc --with-cmodel=medlow --enable-multilib && \
	make all install

pulp-sdk:
	cd toolchain/pulp-sdk && \
	source configs/mempool.sh && source configs/platform-gvsoc.sh && \
	make clean all env

app:
	cd apps/gradient && \
	make clean gradient all disdump run
