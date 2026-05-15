# Copyright 2021 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

APPS_OMP_DIR       := $(APPS_DIR)/omp
APPS_OMP           := $(patsubst $(APPS_OMP_DIR)/%/main.c,%,$(shell find $(APPS_OMP_DIR) -name "main.c"))
APPS_OMP_BIN_DIR   := $(SW_DIR)/bin/apps/omp
APPS_OMP_BINARIES  := $(addprefix $(APPS_OMP_BIN_DIR)/,$(APPS_OMP))

TESTS_OMP_DIR      := $(TESTS_DIR)/omp
TESTS_OMP          := $(patsubst $(TESTS_OMP_DIR)/%/main.c,%,$(shell find $(TESTS_OMP_DIR) -name "main.c"))
TESTS_OMP_BIN_DIR  := $(SW_DIR)/bin/tests/omp
TESTS_OMP_BINARIES := $(addprefix $(TESTS_OMP_BIN_DIR)/,$(TESTS_OMP))

OMP_RISCV_CCFLAGS := $(RISCV_CCFLAGS) -fopenmp -DNTHREADS=$(num_cores) -I$(OMP_DIR)
$(OMP_RUNTIME): RISCV_CCFLAGS := $(OMP_RISCV_CCFLAGS)
$(addsuffix /main.c.o,$(addprefix $(APPS_OMP_DIR)/,$(APPS_OMP))): RISCV_CCFLAGS := $(OMP_RISCV_CCFLAGS)
$(addsuffix /main.c.o,$(addprefix $(TESTS_OMP_DIR)/,$(TESTS_OMP))): RISCV_CCFLAGS := $(OMP_RISCV_CCFLAGS)

$(APPS_OMP_BINARIES): \
$(APPS_OMP_BIN_DIR)/%: $(APPS_OMP_DIR)/%/main.c.o $(RUNTIME) $(OMP_RUNTIME) $(LINKER_SCRIPT) update-opcodes
	mkdir -p $(dir $@)
	$(RISCV_CC) -Iinclude $(RISCV_LDFLAGS) -o $@ $< $(RUNTIME) $(OMP_RUNTIME) -T$(RUNTIME_DIR)/link.ld
	$(RISCV_OBJCOPY) --remove-section=.riscv.attributes $@
	$(RISCV_OBJDUMP) $(RISCV_OBJDUMP_FLAGS) -D $@ > $@.dump

$(TESTS_OMP_BINARIES): \
$(TESTS_OMP_BIN_DIR)/%: $(TESTS_OMP_DIR)/%/main.c.o $(RUNTIME) $(OMP_RUNTIME) $(LINKER_SCRIPT) update-opcodes
	mkdir -p $(dir $@)
	$(RISCV_CC) -Iinclude $(RISCV_LDFLAGS) -o $@ $< $(RUNTIME) $(OMP_RUNTIME) -T$(RUNTIME_DIR)/link.ld
	$(RISCV_OBJCOPY) --remove-section=.riscv.attributes $@
	$(RISCV_OBJDUMP) $(RISCV_OBJDUMP_FLAGS) -D $@ > $@.dump

.PHONY: apps-omp
apps-omp: $(APPS_OMP_BINARIES)

.PHONY: tests-omp
tests-omp: $(TESTS_OMP_BINARIES)

.PHONY: clean-apps-omp
clean-apps-omp:
	rm -vf $(APPS_OMP_BINARIES)
	rm -vf $(addsuffix .dump,$(APPS_OMP_BINARIES))
	rm -vf $(addsuffix /main.c.o,$(addprefix $(APPS_OMP_DIR)/,$(APPS_OMP)))
	rm -vf $(RUNTIME)
	rm -vf $(OMP_RUNTIME)
	rm -vf $(LINKER_SCRIPT)

.PHONY: clean-tests-omp
clean-tests-omp:
	rm -vf $(TESTS_OMP_BINARIES)
	rm -vf $(addsuffix .dump,$(TESTS_OMP_BINARIES))
	rm -vf $(addsuffix /main.c.o,$(addprefix $(TESTS_OMP_DIR)/,$(TESTS_OMP)))
	rm -vf $(RUNTIME)
	rm -vf $(OMP_RUNTIME)
	rm -vf $(LINKER_SCRIPT)

.INTERMEDIATE: $(addsuffix /main.c.o,$(addprefix $(APPS_OMP_DIR)/,$(APPS_OMP)))
.INTERMEDIATE: $(addsuffix /main.c.o,$(addprefix $(TESTS_OMP_DIR)/,$(TESTS_OMP)))
