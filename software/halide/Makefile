# Copyright 2021 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

SHELL = /usr/bin/env bash
ROOT_DIR := $(patsubst %/,%, $(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
SOFTWARE_DIR := $(abspath $(ROOT_DIR)/..)
RUNTIME_DIR := $(abspath $(SOFTWARE_DIR)/runtime)
BIN_DIR := $(abspath $(SOFTWARE_DIR)/bin)
APPS_DIR := $(ROOT_DIR)
# This will overwrite the ROOT_DIR variable from the included Makefile
include $(RUNTIME_DIR)/runtime.mk

RUNTIME += $(RUNTIME_DIR)/halide_runtime.c.o
PIPELINE := halide_pipeline.riscv.o

# Create convenience target
APP_PREFIX := halide-
APPS := $(patsubst $(APPS_DIR)/%/main.c,%,$(shell find $(APPS_DIR) -name "main.c"))
BINARIES := $(addprefix $(BIN_DIR)/$(APP_PREFIX),$(APPS))

# Make all applications
all: $(BINARIES)

# RISC-V applications
$(APPS): % : $(BIN_DIR)/$(APP_PREFIX)% $(APPS_DIR)/Makefile $(shell find $(RUNTIME_DIR)/**.{S,c,h,ld} -type f)

.PHONY: $(BINARIES)
$(BINARIES):  $(BIN_DIR)/$(APP_PREFIX)%: %/$(PIPELINE) %/main.c.o $(RUNTIME) $(LINKER_SCRIPT)
	mkdir -p $(dir $@)
	$(RISCV_CC) -I$(HALIDE_INCLUDE) $(RISCV_LDFLAGS) -o $@ $(filter-out $(LINKER_SCRIPT),$^) -T$(RUNTIME_DIR)/link.ld
	$(RISCV_OBJDUMP) $(RISCV_OBJDUMP_FLAGS) -D $@ > $@.dump
	$(RISCV_STRIP) $@ -S --strip-unneeded

# Build Halide application
%.bin: %.cpp
	$(CXX) $< -g -I $(HALIDE_INCLUDE) -L$(HALIDE_LIB) $(DEFINES) -lHalide -lpthread -ldl -std=c++11 -o $@

# Run Halide cross-compilation
%.riscv.o: %.bin
	cd $(dir $*) && LD_LIBRARY_PATH=$(HALIDE_LIB) ./$(notdir $<)

# Helper targets
.PHONY: clean
clean:
	rm -vf $(BINARIES)
	rm -vf $(addsuffix .dump,$(BINARIES))
	rm -vf $(addsuffix /main.c.o,$(APPS))
	rm -vf $(shell find $(APPS) -name "*.riscv.*")
	rm -vf $(RUNTIME)
	rm -vf $(LINKER_SCRIPT)

.INTERMEDIATE: $(RUNTIME) $(addsuffix /main.c.o,$(APPS))
