# Copyright 2021 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

SHELL = /usr/bin/env bash
ROOT_DIR := $(patsubst %/,%, $(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
APPS_DIR := $(ROOT_DIR)/apps
RUNTIME_DIR := $(ROOT_DIR)/runtime
TESTS_DIR := $(ROOT_DIR)/riscv-tests/isa
TOOLCHAIN_DIR := $(abspath $(ROOT_DIR)/../toolchain)
# This will overwrite the ROOT_DIR variable from the included makefile
include $(RUNTIME_DIR)/runtime.mk
include $(TESTS_DIR)/snitch_isa.mk

# Applications
.PHONY: apps
apps:
	make -C $(APPS_DIR) all

.PHONY: clean-apps
clean-apps:
	make -C $(APPS_DIR) clean

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

test: update_opcodes $(TESTS)

clean-test:
	rm -vf $(RUNTIME)
	rm -vf $(LINKER_SCRIPT)
	rm -vf $(TESTS)
	rm -vf $(addsuffix .dump,$(TESTS))

# Helper targets
.PHONY: update_opcodes
update_opcodes:
	make -C $(TOOLCHAIN_DIR)/riscv-opcodes all

.PHONY: clean
clean: clean-test clean-apps
