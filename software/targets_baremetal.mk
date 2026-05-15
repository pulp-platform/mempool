# Copyright 2021 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

APPS_BAREMETAL_FP_SUFFIXES   := f16 f32 f8
APPS_BAREMETAL_I_SUFFIXES    := q16 q32 i16 i32 i8
APPS_BAREMETAL_DIR           := $(APPS_DIR)/baremetal
APPS_BAREMETAL_BIN_DIR       := ./bin/apps/baremetal
TESTS_BAREMETAL_DIR          := $(TESTS_DIR)/baremetal
TESTS_BAREMETAL_BIN_DIR      := ./bin/tests/baremetal

APPS_BAREMETAL               := $(patsubst $(APPS_BAREMETAL_DIR)/%/main.c,%,$(shell find $(APPS_BAREMETAL_DIR) -name "main.c"))
APPS_BAREMETAL_GCC_APPS      := $(filter-out $(foreach suf,$(APPS_BAREMETAL_FP_SUFFIXES),$(filter %_$(suf),$(APPS_BAREMETAL))),$(APPS_BAREMETAL))
APPS_BAREMETAL_LLVM_APPS     := $(filter-out $(foreach suf,$(APPS_BAREMETAL_I_SUFFIXES),$(filter %_$(suf),$(APPS_BAREMETAL))),$(APPS_BAREMETAL))
APPS_BAREMETAL_BINARIES      := $(addprefix $(APPS_BAREMETAL_BIN_DIR)/,$(APPS_BAREMETAL))
APPS_BAREMETAL_GCC_BINARIES  := $(addprefix $(APPS_BAREMETAL_BIN_DIR)/,$(APPS_BAREMETAL_GCC_APPS))
APPS_BAREMETAL_LLVM_BINARIES := $(addprefix $(APPS_BAREMETAL_BIN_DIR)/,$(APPS_BAREMETAL_LLVM_APPS))

TESTS_BAREMETAL              := $(patsubst $(TESTS_BAREMETAL_DIR)/%/main.c,%,$(shell find $(TESTS_BAREMETAL_DIR) -name "main.c"))
TESTS_BAREMETAL_BINARIES     := $(addprefix $(TESTS_BAREMETAL_BIN_DIR)/,$(TESTS_BAREMETAL))

$(APPS_BAREMETAL_BINARIES): \
$(APPS_BAREMETAL_BIN_DIR)/%: $(APPS_BAREMETAL_DIR)/%/main.c.o $(RUNTIME) $(LINKER_SCRIPT) data_%.h update-opcodes
	mkdir -p $(dir $@)
	$(RISCV_CC) -Iinclude $(RISCV_LDFLAGS) -o $@ $< $(RUNTIME) -T$(RUNTIME_DIR)/link.ld
	$(RISCV_OBJCOPY) --remove-section=.riscv.attributes $@
	$(RISCV_OBJDUMP) $(RISCV_OBJDUMP_FLAGS) -D $@ > $@.dump

$(TESTS_BAREMETAL_BINARIES): \
$(TESTS_BAREMETAL_BIN_DIR)/%: $(TESTS_BAREMETAL_DIR)/%/main.c.o $(RUNTIME) $(LINKER_SCRIPT) data_%.h update-opcodes
	mkdir -p $(dir $@)
	$(RISCV_CC) -Iinclude $(RISCV_LDFLAGS) -o $@ $< $(RUNTIME) -T$(RUNTIME_DIR)/link.ld
	$(RISCV_OBJCOPY) --remove-section=.riscv.attributes $@
	$(RISCV_OBJDUMP) $(RISCV_OBJDUMP_FLAGS) -D $@ > $@.dump

.PHONY: apps-baremetal
apps-baremetal: apps-baremetal-gcc

.PHONY: apps-baremetal-gcc
apps-baremetal-gcc: $(APPS_BAREMETAL_GCC_BINARIES)

.PHONY: apps-baremetal-llvm
apps-baremetal-llvm: $(APPS_BAREMETAL_LLVM_BINARIES)

.PHONY: tests-baremetal
tests-baremetal: $(TESTS_BAREMETAL_BINARIES)

.PHONY: clean-apps-baremetal
clean-apps-baremetal:
	rm -vf $(APPS_BAREMETAL_BINARIES)
	rm -vf $(addsuffix .dump,$(APPS_BAREMETAL_BINARIES))
	rm -vf $(addsuffix /main.c.o,$(addprefix $(APPS_BAREMETAL_DIR)/,$(APPS_BAREMETAL)))
	rm -vf $(RUNTIME)
	rm -vf $(LINKER_SCRIPT)
	rm -vf $(wildcard $(DATA_DIR)/data_*.h)

.PHONY: clean-tests-baremetal
clean-tests-baremetal:
	rm -vf $(TESTS_BAREMETAL_BINARIES)
	rm -vf $(addsuffix .dump,$(TESTS_BAREMETAL_BINARIES))
	rm -vf $(addsuffix /main.c.o,$(addprefix $(TESTS_BAREMETAL_DIR)/,$(TESTS_BAREMETAL)))
	rm -vf $(RUNTIME)
	rm -vf $(LINKER_SCRIPT)

.INTERMEDIATE: $(addsuffix /main.c.o,$(addprefix $(APPS_BAREMETAL_DIR)/,$(APPS_BAREMETAL)))
.INTERMEDIATE: $(addsuffix /main.c.o,$(addprefix $(TESTS_BAREMETAL_DIR)/,$(TESTS_BAREMETAL)))
