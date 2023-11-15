# Copyright 2021 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

SHELL = /usr/bin/env bash
ROOT_DIR := $(patsubst %/,%, $(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
MEMPOOL_DIR := $(shell git rev-parse --show-toplevel 2>/dev/null || echo $$MEMPOOL_DIR)
APPS_DIR := $(ROOT_DIR)/apps
BIN_DIR := $(ROOT_DIR)/bin
HALIDE_DIR := $(ROOT_DIR)/halide
RUNTIME_DIR := $(ROOT_DIR)/runtime
TESTS_DIR := $(ROOT_DIR)/riscv-tests/isa
TOOLCHAIN_DIR := $(abspath $(ROOT_DIR)/../toolchain)
# This will overwrite the ROOT_DIR variable from the included makefile
include $(RUNTIME_DIR)/runtime.mk
include $(TESTS_DIR)/snitch_isa.mk
include $(TESTS_DIR)/spatz.mk

# Applications
.PHONY: apps
apps:
	make -C $(APPS_DIR) all

.PHONY: halide-apps
halide-apps:
	make -C $(HALIDE_DIR) all

.PHONY: clean-apps
clean-apps:
	make -C $(APPS_DIR) clean

.PHONY: clean-halide-apps
clean-halide-apps:
	make -C $(HALIDE_DIR) clean

# Unit tests
TESTS := $(addprefix bin/,$(rtl_mempool_tests))

define rtl_mempool_tests_template

TESTS_$(1) := $(addprefix bin/,$($(1)_mempool_tests))

$$(TESTS_$(1)): bin/$(1)-mempool-%: $(TESTS_DIR)/$(1)/%.S $(LINKER_SCRIPT)
	mkdir -p $$(shell dirname $$@)
	$$(RISCV_CC) $$(RISCV_CCFLAGS_TESTS) -T$$(RUNTIME_DIR)/link.ld $$< -o $$@
	$$(RISCV_STRIP) $$@ -g -S -d --strip-debug
	$$(RISCV_OBJDUMP) $(RISCV_OBJDUMP_FLAGS) -D $$@ > $$@.dump

endef

$(eval $(call rtl_mempool_tests_template,rv32ui))
$(eval $(call rtl_mempool_tests_template,rv32um))
$(eval $(call rtl_mempool_tests_template,rv32ua))
$(eval $(call rtl_mempool_tests_template,rv32uxpulpimg))
$(eval $(call rtl_mempool_tests_template,rv32uf))

TESTS_rv32uv := $(addprefix $(BIN_DIR)/, $(rv32uv_spatz_tests))

$(BIN_DIR)/rv32uv-spatz-%: $(TESTS_DIR)/rv32uv/%.c $(RUNTIME) $(LINKER_SCRIPT)
	mkdir -p $(BIN_DIR)
	$(RISCV_CC) -Iinclude -I$(TESTS_DIR)/macros/scalar -I$(TESTS_DIR)/macros/vector $(RISCV_LDFLAGS_TESTS) -o $@ $< $(RUNTIME) -T$(RUNTIME_DIR)/link.ld
	$(RISCV_OBJDUMP) $(RISCV_OBJDUMP_FLAGS) -D $@ > $@.dump

test: update_opcodes $(TESTS)
test_spatz: update_opcodes $(TESTS_rv32uv)

clean-test:
	rm -vf $(RUNTIME)
	rm -vf $(LINKER_SCRIPT)
	rm -vf $(TESTS)
	rm -vf $(addsuffix .dump,$(TESTS))
	rm -vf $(TESTS_rv32uv)
	rm -vf $(addsuffix .dump,$(TESTS_rv32uv))

# Helper targets
update_opcodes:
	make -C $(MEMPOOL_DIR) update_opcodes

.PHONY: clean
clean: clean-test clean-apps clean-halide-apps
