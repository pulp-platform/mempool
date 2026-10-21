# Copyright 2021 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Author: Samuel Riedel, ETH Zurich

SHELL = /usr/bin/env bash
ROOT_DIR := $(patsubst %/,%, $(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
MEMPOOL_DIR := $(shell git rev-parse --show-toplevel 2>/dev/null || echo $$MEMPOOL_DIR)
SOFTWARE_DIR := $(abspath $(ROOT_DIR)/../..)
TESTS_DIR := $(ROOT_DIR)
BIN_DIR := $(abspath $(SOFTWARE_DIR)/bin/$(subst $(SOFTWARE_DIR),,$(TESTS_DIR)))
DATA_DIR := $(abspath $(SOFTWARE_DIR)/data)
RUNTIME_DIR := $(abspath $(SOFTWARE_DIR)/runtime)
# This will overwrite the ROOT_DIR variable from the included makefile
include $(RUNTIME_DIR)/runtime.mk

TESTS := $(patsubst $(TESTS_DIR)/%/main.c,%,$(shell find $(TESTS_DIR) -name "main.c"))
BINARIES := $(addprefix $(BIN_DIR)/,$(TESTS))

# Tests whose main.c actually #includes a generated data_<test>.h: make that
# header an explicit prerequisite of their compiled object. Forcing data_%.h
# unconditionally on every test (as the $(BINARIES) recipe used to, below)
# makes any test with no HJSON entry -- and no need for one -- fail outright,
# since data_%.h's recipe still tries (and fails) to generate it regardless.
DATA_TESTS := $(foreach t,$(TESTS),$(if $(shell grep -l 'include "data_$(t)\.h"' $(TESTS_DIR)/$(t)/main.c 2>/dev/null),$(t)))
$(foreach t,$(DATA_TESTS),$(eval $(t)/main.c.o: $(DATA_DIR)/data_$(t).h))

# Make all applications
all: $(TESTS)

$(TESTS): % : $(BIN_DIR)/% $(TESTS_DIR)/Makefile $(shell find $(RUNTIME_DIR)/**.{S,c,h,ld} -type f)

.PHONY: $(BINARIES)
$(BINARIES): $(BIN_DIR)/%: %/main.c.o $(RUNTIME) $(LINKER_SCRIPT) update-opcodes
	mkdir -p $(dir $@)
	$(RISCV_CC) -Iinclude $(RISCV_LDFLAGS) -o $@ $< $(RUNTIME) -T$(RUNTIME_DIR)/link.ld
	$(RISCV_OBJDUMP) $(RISCV_OBJDUMP_FLAGS) -D $@ > $@.dump

# Helper targets
update-opcodes:
	make -C $(MEMPOOL_DIR) update-opcodes

.PHONY: clean
clean:
	rm -vf $(BINARIES)
	rm -vf $(addsuffix .dump,$(BINARIES))
	rm -vf $(addsuffix /main.c.o,$(TESTS))
	rm -vf $(RUNTIME)
	rm -vf $(LINKER_SCRIPT)

.INTERMEDIATE: $(addsuffix /main.c.o,$(TESTS))
