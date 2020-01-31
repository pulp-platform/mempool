ROOT := $(patsubst %/,%, $(dir $(abspath $(lastword $(MAKEFILE_LIST)))))

# Toolchain
.PHONY: tc-gcc

tc-gcc: submodules
	mkdir -p $(CURDIR)/output/tc-gcc
	cd $(CURDIR)/toolchain/riscv-gnu-toolchain && ./configure --prefix=$(CURDIR)/output/tc-gcc --enable-multilib && $(MAKE)

# Helper targets
.PHONY: submodules clean

submodules:
	git submodule update --init --recursive

clean:
	rm -rf $(CURDIR)/output/*
