# Copyright 2021 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

SHELL = /usr/bin/env bash
ROOT_DIR := $(patsubst %/,%, $(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
MEMPOOL_DIR := $(shell git rev-parse --show-toplevel 2>/dev/null || echo $$MEMPOOL_DIR)
SW_DIR := $(ROOT_DIR)
APPS_DIR := $(ROOT_DIR)/apps
HALIDE_DIR := $(ROOT_DIR)/halide
RUNTIME_DIR := $(ROOT_DIR)/runtime
TESTS_DIR := $(ROOT_DIR)/tests
RISCV_TESTS_DIR := $(ROOT_DIR)/riscv-tests/isa
TOOLCHAIN_DIR := $(abspath $(ROOT_DIR)/../toolchain)
# This will overwrite the ROOT_DIR variable from the included makefile
include $(RUNTIME_DIR)/runtime.mk
include $(SW_DIR)/snitch_isa.mk

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

# Helper targets
update-opcodes:
	make -C $(MEMPOOL_DIR) update-opcodes

include $(SW_DIR)/riscv_tests.mk

.PHONY: clean
clean: clean-tests clean-apps clean-riscv-test
