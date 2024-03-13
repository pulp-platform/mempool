# Copyright 2021 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Author: Samuel Riedel, ETH Zurich

SHELL = /usr/bin/env bash
ROOT_DIR := $(patsubst %/,%, $(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
MEMPOOL_DIR := $(shell git rev-parse --show-toplevel 2>/dev/null || echo $$MEMPOOL_DIR)
SOFTWARE_DIR := $(abspath $(ROOT_DIR)/..)
BIN_DIR := $(abspath $(SOFTWARE_DIR)/bin)
DATA_DIR := $(abspath $(SOFTWARE_DIR)/data)
RUNTIME_DIR := $(abspath $(SOFTWARE_DIR)/runtime)
TESTS_DIR := $(ROOT_DIR)
# This will overwrite the ROOT_DIR variable from the included makefile
include $(RUNTIME_DIR)/runtime.mk

TESTS := $(patsubst $(TESTS_DIR)/%/main.c,%,$(shell find $(TESTS_DIR) -name "main.c"))
DATA := $(patsubst %.args,%.h,$(shell find $(TESTS_DIR) -name "data.args"))
ALLPYS := $(patsubst %.py,%.h,$(wildcard $(DATA_DIR)/*.py))
BINARIES := $(addprefix $(BIN_DIR)/,$(TESTS))

# Make all applications
all: $(TESTS)

$(TESTS): % : $(BIN_DIR)/% $(TESTS_DIR)/Makefile $(shell find $(RUNTIME_DIR)/**.{S,c,h,ld} -type f)

.PHONY: $(BINARIES)
$(BINARIES): $(BIN_DIR)/%: %/main.c.o $(RUNTIME) $(LINKER_SCRIPT) $(DATA) $(ALLPYS) update_opcodes
	mkdir -p $(dir $@)
	$(RISCV_CC) -Iinclude $(RISCV_LDFLAGS) -o $@ $< $(RUNTIME) -T$(RUNTIME_DIR)/link.ld
	$(RISCV_OBJDUMP) $(RISCV_OBJDUMP_FLAGS) -D $@ > $@.dump

# Helper targets
update_opcodes:
	make -C $(MEMPOOL_DIR) update_opcodes

.PHONY: clean
clean:
	rm -vf $(BINARIES)
	rm -vf $(addsuffix .dump,$(BINARIES))
	rm -vf $(addsuffix /main.c.o,$(TESTS))
	rm -vf $(RUNTIME)
	rm -vf $(LINKER_SCRIPT)

.INTERMEDIATE: $(addsuffix /main.c.o,$(TESTS))
