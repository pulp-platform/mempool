# Copyright 2024 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

SHELL = /usr/bin/env bash
ROOT_DIR := $(patsubst %/,%, $(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
MEMPOOL_DIR := $(shell git rev-parse --show-toplevel 2>/dev/null || echo $$MEMPOOL_DIR)
SOFTWARE_DIR := $(abspath $(ROOT_DIR)/..)

BUILD_TARGETS := $(patsubst $(ROOT_DIR)/%,%,$(shell find $(ROOT_DIR) -mindepth 1 -maxdepth 1 -type d))
CLEAN_TARGETS := $(addprefix clean-,$(BUILD_TARGETS))

# Make all applications
all: $(BUILD_TARGETS)

.PHONY: $(BUILD_TARGETS)
$(BUILD_TARGETS):
	make -C $@ all

# Clean all applications
.PHONY: clean
clean: $(CLEAN_TARGETS)

.PHONY: $(CLEAN_TARGETS)
$(CLEAN_TARGETS): clean-% :
	make -C $* clean
