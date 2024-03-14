# Copyright 2021 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

SHELL = /usr/bin/env bash
ROOT_DIR := $(patsubst %/,%, $(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
MEMPOOL_DIR := $(shell git rev-parse --show-toplevel 2>/dev/null || echo $$MEMPOOL_DIR)
APPS_DIR := $(ROOT_DIR)/apps
HALIDE_DIR := $(ROOT_DIR)/halide
RUNTIME_DIR := $(ROOT_DIR)/runtime
TESTS_DIR := $(ROOT_DIR)/tests
RISCV_TESTS_DIR := $(ROOT_DIR)/riscv-tests/isa
TOOLCHAIN_DIR := $(abspath $(ROOT_DIR)/../toolchain)
# This will overwrite the ROOT_DIR variable from the included makefile
include $(RUNTIME_DIR)/runtime.mk
include $(RISCV_TESTS_DIR)/snitch_isa.mk

# Applications
.PHONY: apps
apps:
	make -C $(APPS_DIR) all

.PHONY: tests
tests:
	make -C $(TESTS_DIR) all

.PHONY: clean-apps
clean-apps:
	make -C $(APPS_DIR) clean

.PHONY: clean-tests
clean-tests:
	make -C $(TESTS_DIR) clean

# Unit tests
RISCV_TESTS := $(addprefix bin/,$(rtl_mempool_tests))

define rtl_mempool_tests_template

RISCV-TESTS-$(1) := $(addprefix bin/,$($(1)_mempool_tests))

$$(RISCV-TESTS-$(1)): bin/$(1)-mempool-%: $(RISCV_TESTS_DIR)/$(1)/%.S $(LINKER_SCRIPT)
	mkdir -p $$(shell dirname $$@)
	$$(RISCV_CC) $$(RISCV_CCFLAGS_TESTS) -T$$(RUNTIME_DIR)/link.ld $$< -o $$@
	$$(RISCV_STRIP) $$@ -g -S -d --strip-debug
	$$(RISCV_OBJDUMP) $(RISCV_OBJDUMP_FLAGS) -D $$@ > $$@.dump

endef

$(eval $(call rtl_mempool_tests_template,rv32ui))
$(eval $(call rtl_mempool_tests_template,rv32um))
$(eval $(call rtl_mempool_tests_template,rv32ua))
$(eval $(call rtl_mempool_tests_template,rv32uxpulpimg))

riscv-tests: update_opcodes $(RISCV_TESTS)

clean-riscv-test:
	rm -vf $(RUNTIME)
	rm -vf $(LINKER_SCRIPT)
	rm -vf $(RISCV_TESTS)
	rm -vf $(addsuffix .dump,$(RISCV_TESTS))

# Helper targets
update_opcodes:
	make -C $(MEMPOOL_DIR) update_opcodes

.PHONY: clean
clean: clean-test clean-apps clean-halide-apps
