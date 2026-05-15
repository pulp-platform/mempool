# Copyright 2021 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

APPS_HALIDE_DIR      := $(APPS_DIR)/halide
APPS_HALIDE_BIN_DIR  := ./bin/apps/halide
APPS_HALIDE          := $(patsubst $(APPS_HALIDE_DIR)/%/main.c,%,$(shell find $(APPS_HALIDE_DIR) -name "main.c"))
APPS_HALIDE_BINARIES := $(addprefix $(APPS_HALIDE_BIN_DIR)/,$(APPS_HALIDE))

HALIDE_INSTALL_DIR   ?= $(INSTALL_DIR)/halide
HALIDE_INCLUDE       ?= $(HALIDE_INSTALL_DIR)/include
HALIDE_LIB           ?= $(HALIDE_INSTALL_DIR)/lib
HALIDE_RUNTIME_DIR   := $(RUNTIME_DIR)/halide
HALIDE_RUNTIME_OBJ   := $(HALIDE_RUNTIME_DIR)/halide_runtime.c.o
HALIDE_PIPELINE      := halide_pipeline.riscv.o
HALIDE_RUNTIME_OBJS  := $(RUNTIME) $(HALIDE_RUNTIME_OBJ)
HALIDE_CCFLAGS       := $(RISCV_CCFLAGS) -I$(HALIDE_INCLUDE) -I$(HALIDE_RUNTIME_DIR)

$(HALIDE_RUNTIME_OBJ): RISCV_CCFLAGS := $(HALIDE_CCFLAGS)
$(addsuffix /main.c.o,$(addprefix $(APPS_HALIDE_DIR)/,$(APPS_HALIDE))): RISCV_CCFLAGS := $(HALIDE_CCFLAGS)

.PHONY: apps-halide
apps-halide: $(APPS_HALIDE_BINARIES)

$(APPS_HALIDE_BINARIES): \
$(APPS_HALIDE_BIN_DIR)/%: $(APPS_HALIDE_DIR)/%/$(HALIDE_PIPELINE) $(APPS_HALIDE_DIR)/%/main.c.o $(HALIDE_RUNTIME_OBJS) $(LINKER_SCRIPT)
	mkdir -p $(dir $@)
	$(RISCV_CC) -I$(HALIDE_INCLUDE) $(RISCV_LDFLAGS) -o $@ $(filter-out $(LINKER_SCRIPT),$^) -T$(RUNTIME_DIR)/link.ld
	$(RISCV_OBJCOPY) --remove-section=.riscv.attributes $@
	$(RISCV_OBJDUMP) $(RISCV_OBJDUMP_FLAGS) -D $@ > $@.dump

%.bin: %.cpp
	$(CXX) $< -g -I $(HALIDE_INCLUDE) -L$(HALIDE_LIB) $(DEFINES) -lHalide -lpthread -ldl -std=c++17 -o $@

%.riscv.o: %.bin
	cd $(dir $*) && LD_LIBRARY_PATH=$(HALIDE_LIB) ./$(notdir $<)

.PHONY: clean-apps-halide
clean-apps-halide:
	rm -vf $(APPS_HALIDE_BINARIES)
	rm -vf $(addsuffix .dump,$(APPS_HALIDE_BINARIES))
	rm -vf $(addsuffix /main.c.o,$(addprefix $(APPS_HALIDE_DIR)/,$(APPS_HALIDE)))
	rm -vf $(shell find $(addprefix $(APPS_HALIDE_DIR)/,$(APPS_HALIDE)) -name "*.riscv.*")
	rm -vf $(HALIDE_RUNTIME_OBJS)
	rm -vf $(LINKER_SCRIPT)

.INTERMEDIATE: $(HALIDE_RUNTIME_OBJS) $(addsuffix /main.c.o,$(addprefix $(APPS_HALIDE_DIR)/,$(APPS_HALIDE)))
