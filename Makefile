ROOT_DIR := $(patsubst %/,%, $(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
SHELL = bash

INSTALL_PREFIX ?= install
INSTALL_DIR    ?= ${ROOT_DIR}/${INSTALL_PREFIX}

CMAKE ?= cmake-3.7.1
CC    ?= gcc-8.2.0
CXX   ?= g++-8.2.0

# Halide
halide: toolchain
	mkdir -p $(INSTALL_DIR)
	cd toolchain/halide && mkdir -p build && cd build; \
	$(CMAKE) \
		-DLLVM_DIR=$(INSTALL_DIR)/lib/cmake/llvm \
		-DCMAKE_INSTALL_PREFIX=$(INSTALL_DIR) \
		-DCMAKE_CXX_COMPILER=$(CXX) \
		-DCMAKE_C_COMPILER=$(CC) \
		-DCMAKE_BUILD_TYPE=Release \
		.. && \
	make -j4 all && \
	make install

# Toolchain
toolchain: tc-riscv-gcc tc-llvm

tc-riscv-gcc:
	mkdir -p ${INSTALL_DIR}
	cd $(CURDIR)/toolchain/riscv-gnu-toolchain && git submodule update --init --recursive && ./configure --prefix=${INSTALL_DIR} --with-arch=rv32im --with-cmodel=medlow --enable-multilib && $(MAKE) -j4

tc-llvm:
	mkdir -p ${INSTALL_DIR}
	cd $(CURDIR)/toolchain/llvm-project && mkdir -p build && cd build; \
	$(CMAKE) \
		-DCMAKE_INSTALL_PREFIX=$(INSTALL_DIR) \
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
	rm -rf ${INSTALL_DIR}
