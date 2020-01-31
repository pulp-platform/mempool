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

# Toolchain
.PHONY: riscv-gcc llvm

riscv-gcc:
	mkdir -p ${GCC_INSTALL_DIR}
	cd $(CURDIR)/toolchain/riscv-gnu-toolchain && git submodule update --init --recursive && ./configure --prefix=${GCC_INSTALL_DIR} --enable-multilib && $(MAKE)

llvm:
	mkdir -p ${LLVM_INSTALL_DIR}
	cd $(CURDIR)/toolchain/llvm-project && mkdir -p build && cd build; pwd; \
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


# Helper targets
.PHONY: clean

clean:
	rm -rf ${INSTALL_DIR}
