# Copyright 2024 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

SHELL = /usr/bin/env bash

ROOT_DIR     := $(patsubst %/,%, $(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
APPS_DIR     := $(ROOT_DIR)
MEMPOOL_DIR  := $(shell git rev-parse --show-toplevel 2>/dev/null || echo $$MEMPOOL_DIR)
SOFTWARE_DIR := $(abspath $(ROOT_DIR)/..)
BIN_DIR      := $(abspath $(SOFTWARE_DIR)/bin)
RUNTIME_DIR  := $(abspath $(SOFTWARE_DIR)/runtime)

# This will overwrite the ROOT_DIR variable from the included makefile
include $(RUNTIME_DIR)/runtime.mk

#############
# Baremetal #
#############

APPS      := $(patsubst $(APPS_DIR)/%/main.c,%,$(shell find $(APPS_DIR)/blas -name "main.c"))
APPS      += $(patsubst $(APPS_DIR)/%/main.c,%,$(shell find $(APPS_DIR)/gnb -name "main.c"))
APPS      += $(patsubst $(APPS_DIR)/%/main.c,%,$(shell find $(APPS_DIR)/nn -name "main.c"))
BINS      := $(addprefix $(BIN_DIR)/,$(APPS))
ALL_LLVM  := $(foreach suf, f16 f32 f8, $(filter %_$(suf), $(APPS)))
ALL_GCC   := $(filter-out $(ALL_LLVM),$(APPS))

# convenience targets
$(foreach a,$(APPS),$(eval $(a): data_$(notdir $(a))))
$(APPS): % : $(BIN_DIR)/% $(APPS_DIR)/Makefile $(shell find $(RUNTIME_DIR)/**.{S,c,h,ld} -type f)

# Link all objects to the binaries
$(BINS): $(BIN_DIR)/%: %/main.c.o $(RUNTIME) $(LINKER_SCRIPT) update_opcodes
	mkdir -p $(dir $@)
	$(RISCV_CC) -Iinclude -o $@ $< $(RUNTIME) $(RISCV_LDFLAGS) -T$(RUNTIME_DIR)/link.ld
	$(RISCV_OBJDUMP) $(RISCV_OBJDUMP_FLAGS) -D $@ > $@.dump

# --- data rule ---
data_%: $(DATA_DIR)/gendata_params.hjson
	$(python) $(DATA_DIR)/gendata_header.py --app_name $* --params $<

############
# Systolic #
############

SYSTOLIC_APPS := $(patsubst $(APPS_DIR)/%/main.c,%,$(shell find $(APPS_DIR)/systolic -name "main.c"))
SYSTOLIC_BINS := $(addprefix $(BIN_DIR)/,$(SYSTOLIC_APPS))

# Create convenience target
$(SYSTOLIC_APPS): % : $(BIN_DIR)/% $(APPS_DIR)/Makefile $(shell find $(RUNTIME_DIR)/**.{S,c,h,ld} -type f)

# Check if the config is set to systolic and link
ifeq ($(config),systolic)
$(SYSTOLIC_BINS): $(BIN_DIR)/%: %/main.c.o $(RUNTIME) $(LINKER_SCRIPT) update_opcodes
	mkdir -p $(dir $@)
	$(RISCV_CC) -Iinclude $(RISCV_LDFLAGS) -o $@ $< $(RUNTIME) -T$(RUNTIME_DIR)/link.ld
	$(RISCV_OBJDUMP) $(RISCV_OBJDUMP_FLAGS) -D $@ > $@.dump
else
$(SYSTOLIC_BINS):
	# Error message if config is not systolic
	$(error "Config ($(config)) must be systolic to build systolic applications.")
endif

##########
# OpenMP #
##########

# OpenMP runtime
OMP_RUNTIME_DIR   := $(RUNTIME_DIR)/omp
OMP_RISCV_CCFLAGS := -fopenmp -DNTHREADS=$(num_cores)
OMP_RISCV_CCFLAGS += -I$(OMP_DIR)

# Create convenience target
OMP_APPS := $(patsubst $(APPS_DIR)/%/main.c,%,$(shell find $(APPS_DIR)/omp -name "main.c"))
OMP_BINS := $(addprefix $(BIN_DIR)/,$(OMP_APPS))
$(OMP_APPS): % : $(BIN_DIR)/% $(APPS_DIR)/Makefile $(shell find $(RUNTIME_DIR)/**.{S,c,h,ld} -type f)

# Add flags to compile OpenMP binaries and runtime
$(OMP_APPS:%=%/%.o): RISCV_CCFLAGS += $(OMP_RISCV_CCFLAGS)
$(OMP_RUNTIME): RISCV_CCFLAGS += $(OMP_RISCV_CCFLAGS)

# Link all objects to the binaries
$(OMP_BINS): $(BIN_DIR)/%: %/main.c.o $(RUNTIME) $(OMP_RUNTIME) $(LINKER_SCRIPT) update_opcodes
	mkdir -p $(dir $@)
	$(RISCV_CC) -Iinclude $(RISCV_LDFLAGS) -o $@ $< $(RUNTIME) $(OMP_RUNTIME) -T$(RUNTIME_DIR)/link.ld
	$(RISCV_OBJDUMP) $(RISCV_OBJDUMP_FLAGS) -D $@ > $@.dump

##########
# Halide #
##########

# Halide install
HALIDE_INSTALL_DIR   ?= $(INSTALL_DIR)/halide
HALIDE_INCLUDE       ?= $(HALIDE_INSTALL_DIR)/include
HALIDE_LIB           ?= $(HALIDE_INSTALL_DIR)/lib

# Halide runtime
HALIDE_RUNTIME_DIR   := $(abspath $(RUNTIME_DIR)/halide)
HALIDE_RISCV_CCFLAGS := -I$(HALIDE_INCLUDE) -I$(HALIDE_RUNTIME_DIR)
HALIDE_PIPELINE      := halide_pipeline.riscv.o

# Create convenience target
HALIDE_APPS := $(patsubst $(APPS_DIR)/%/main.c,%,$(shell find $(APPS_DIR)/halide -name "main.c"))
HALIDE_BINS := $(addprefix $(BIN_DIR)/,$(HALIDE_APPS))
$(HALIDE_APPS): % : $(BIN_DIR)/% $(APPS_DIR)/Makefile $(shell find $(RUNTIME_DIR)/**.{S,c,h,ld} -type f)

# Add flags to compile Halide binaries and runtime
$(HALIDE_APPS:%=%/%.c.o): RISCV_CCFLAGS += $(HALIDE_RISCV_CCFLAGS)
$(HALIDE_RUNTIME): RISCV_CCFLAGS += $(HALIDE_RISCV_CCFLAGS)

# Link all objects to the binaries
$(HALIDE_BINS):  $(BIN_DIR)/%: %/$(HALIDE_PIPELINE) %/main.c.o $(RUNTIME) $(HALIDE_RUNTIME) $(LINKER_SCRIPT)
	mkdir -p $(dir $@)
	$(RISCV_CC) -I$(HALIDE_INCLUDE) $(RISCV_LDFLAGS) -o $@ $(filter-out $(LINKER_SCRIPT),$^) -T$(RUNTIME_DIR)/link.ld
	$(RISCV_OBJDUMP) $(RISCV_OBJDUMP_FLAGS) -D $@ > $@.dump

# Add Halide-specific rule to build Halide application
%.bin: %.cpp
	$(CXX) $< -g -I $(HALIDE_INCLUDE) -L$(HALIDE_LIB) $(DEFINES) -lHalide -lpthread -ldl -std=c++17 -o $@

# Add Halide-specific rule to run Halide cross-compilation
%.riscv.o: %.bin
	cd $(dir $*) && LD_LIBRARY_PATH=$(HALIDE_LIB) ./$(notdir $<)

##################
# Helper targets #
##################

# Make all applications
all: $(ALL_GCC) $(OMP_APPS) $(HALIDE_APPS)
all-llvm: $(ALL_LLVM)
all-gcc: $(ALL_GCC)

# Update the opcodes
update_opcodes:
	make -C $(MEMPOOL_DIR) update_opcodes

# Clean targets
clean-runtime:
	rm -vf $(RUNTIME) $(LINKER_SCRIPT)

clean-apps: clean-runtime
	rm -vf $(BINS) $(addsuffix .dump,$(BINS))
	rm -vf $(addsuffix /main.c.o,$(APPS))
	rm -vf $(wildcard $(DATA_DIR)/data_*.h)

clean-systolic: clean-runtime
	rm -vf $(SYSTOLIC_BINS) $(addsuffix .dump,$(SYSTOLIC_BINS))
	rm -vf $(addsuffix /main.c.o,$(SYSTOLIC_APPS))

clean-omp: clean-runtime
	rm -vf $(OMP_BINS) $(addsuffix .dump,$(OMP_BINS))
	rm -vf $(addsuffix /main.c.o,$(OMP_APPS))
	rm -vf $(OMP_RUNTIME)

clean-halide: clean-runtime
	rm -vf $(HALIDE_BINS) $(addsuffix .dump,$(HALIDE_BINS))
	rm -vf $(addsuffix /main.c.o,$(HALIDE_APPS))
	rm -vf $(shell find $(HALIDE_APPS) -name "*.riscv.*")
	rm -vf $(HALIDE_RUNTIME)

.PHONY: clean
clean: clean-apps clean-omp clean-halide
