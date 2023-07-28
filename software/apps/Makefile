# Copyright 2024 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

SHELL = /usr/bin/env bash
ROOT_DIR := $(patsubst %/,%, $(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
MEMPOOL_DIR := $(shell git rev-parse --show-toplevel 2>/dev/null || echo $$MEMPOOL_DIR)
SOFTWARE_DIR := $(abspath $(ROOT_DIR)/..)
RUNTIME_DIR := $(abspath $(SOFTWARE_DIR)/runtime)
BIN_DIR := $(abspath $(SOFTWARE_DIR)/bin)
APPS_DIR := $(ROOT_DIR)
# This will overwrite the ROOT_DIR variable from the included makefile
include $(RUNTIME_DIR)/runtime.mk

APPS := $(patsubst $(APPS_DIR)/%/main.c,%,$(shell find $(APPS_DIR) -name "main.c"))
DATA := $(patsubst %.args,%.h,$(shell find $(APPS_DIR) -name "data.args"))
ALLPYS := $(patsubst %.py,%.h,$(wildcard $(RUNTIME_DIR)/data/*.py))
BINARIES := $(addprefix $(BIN_DIR)/,$(APPS))
ifeq ($(config), systolic)
	ALL := $(APPS)
else
	ALL := $(filter-out systolic/%,$(APPS))
endif

BUILD_TARGETS := $(patsubst $(ROOT_DIR)/%,%,$(shell find $(ROOT_DIR) -mindepth 1 -maxdepth 1 -type d))
CLEAN_TARGETS := $(addprefix clean-,$(BUILD_TARGETS))


# Make all applications
all: $(ALL)

# Make only applications with full llvm support
all_llvm: $(ALL_LLVM)

$(APPS): % : $(BIN_DIR)/% $(APPS_DIR)/Makefile $(shell find $(RUNTIME_DIR)/**.{S,c,h,ld} -type f)

.PHONY: $(BINARIES)
$(BINARIES): $(BIN_DIR)/%: %/main.c.o $(RUNTIME) $(LINKER_SCRIPT) $(DATA) $(ALLPYS) update_opcodes
	mkdir -p $(dir $@)
	$(RISCV_CC) -Iinclude $(RISCV_LDFLAGS) -o $@ $< $(RUNTIME) -T$(RUNTIME_DIR)/link.ld
	$(RISCV_OBJDUMP) $(RISCV_OBJDUMP_FLAGS) -D $@ > $@.dump

.PHONY: $(BUILD_TARGETS)
$(BUILD_TARGETS):
	make -C $@ all

# Clean all applications
.PHONY: clean
clean: $(CLEAN_TARGETS)

.PHONY: $(CLEAN_TARGETS)
$(CLEAN_TARGETS): clean-% :
	make -C $* clean
