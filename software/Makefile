# Copyright 2021 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

SHELL = /usr/bin/env bash

ROOT_DIR        := $(patsubst %/,%, $(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
MEMPOOL_DIR     := $(shell git rev-parse --show-toplevel 2>/dev/null || echo $$MEMPOOL_DIR)
SW_DIR          := $(ROOT_DIR)
APPS_DIR        := $(ROOT_DIR)/apps
RUNTIME_DIR     := $(ROOT_DIR)/runtime
TESTS_DIR       := $(ROOT_DIR)/tests
RISCV_TESTS_DIR := $(ROOT_DIR)/riscv-tests/isa
TOOLCHAIN_DIR   := $(abspath $(ROOT_DIR)/../toolchain)

APPS          := $(patsubst $(APPS_DIR)/%,%,$(shell find $(APPS_DIR) -mindepth 1 -maxdepth 1 -type d | sort))
TESTS         := $(patsubst $(TESTS_DIR)/%,%,$(shell find $(TESTS_DIR) -mindepth 1 -maxdepth 1 -type d | sort))
APPS_TARGETS  := $(addprefix apps-,$(APPS))
TESTS_TARGETS := $(addprefix tests-,$(TESTS))

# This will overwrite the ROOT_DIR variable from the included makefile
include $(RUNTIME_DIR)/runtime.mk

include $(SW_DIR)/snitch_isa.mk
include $(SW_DIR)/targets_baremetal.mk
include $(SW_DIR)/targets_omp.mk
include $(SW_DIR)/targets_systolic.mk
include $(SW_DIR)/targets_halide.mk

# Applications
.PHONY: all
all: apps

.PHONY: apps
apps: $(APPS_TARGETS)

.PHONY: tests
tests: $(TESTS_TARGETS)

.PHONY: clean-apps
clean-apps: $(addprefix clean-apps-,$(APPS))

.PHONY: clean-tests
clean-tests: $(addprefix clean-tests-,$(TESTS))

# Helper targets
update-opcodes:
	make -C $(MEMPOOL_DIR) update-opcodes

include $(SW_DIR)/riscv_tests.mk

.PHONY: clean
clean: clean-tests clean-apps clean-riscv-test
