# Copyright 2021 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

APPS_SYSTOLIC_DIR      := $(APPS_DIR)/systolic
APPS_SYSTOLIC_BIN_DIR  := ./bin/apps/systolic
APPS_SYSTOLIC          := $(patsubst $(APPS_SYSTOLIC_DIR)/%/main.c,%,$(shell find $(APPS_SYSTOLIC_DIR) -name "main.c"))
APPS_SYSTOLIC_BINARIES := $(addprefix $(APPS_SYSTOLIC_BIN_DIR)/,$(APPS_SYSTOLIC))

ifeq ($(config),systolic)
$(APPS_SYSTOLIC_BINARIES): \
$(APPS_SYSTOLIC_BIN_DIR)/%: $(APPS_SYSTOLIC_DIR)/%/main.c.o $(RUNTIME) $(LINKER_SCRIPT) data_%.h update-opcodes
	mkdir -p $(dir $@)
	$(RISCV_CC) -Iinclude $(RISCV_LDFLAGS) -o $@ $< $(RUNTIME) -T$(RUNTIME_DIR)/link.ld
	$(RISCV_OBJCOPY) --remove-section=.riscv.attributes $@
	$(RISCV_OBJDUMP) $(RISCV_OBJDUMP_FLAGS) -D $@ > $@.dump
else
$(APPS_SYSTOLIC_BINARIES):
	$(error "Config ($(config)) must be systolic to build systolic applications.")
endif

.PHONY: apps-systolic
apps-systolic: $(APPS_SYSTOLIC_BINARIES)

.PHONY: clean-apps-systolic
clean-apps-systolic:
	rm -vf $(APPS_SYSTOLIC_BINARIES)
	rm -vf $(addsuffix .dump,$(APPS_SYSTOLIC_BINARIES))
	rm -vf $(addsuffix /main.c.o,$(addprefix $(APPS_SYSTOLIC_DIR)/,$(APPS_SYSTOLIC)))
	rm -vf $(RUNTIME)
	rm -vf $(LINKER_SCRIPT)

.INTERMEDIATE: $(addsuffix /main.c.o,$(addprefix $(APPS_SYSTOLIC_DIR)/,$(APPS_SYSTOLIC)))
