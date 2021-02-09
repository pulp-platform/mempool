# Copyright 2019 ETH Zurich and University of Bologna.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#    http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

# Author: Matheus Cavalcante, ETH Zurich
#         Samuel Riedel, ETH Zurich

SHELL = /usr/bin/env bash
ROOT_DIR := $(patsubst %/,%, $(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
TESTS_DIR := $(ROOT_DIR)/riscv-tests/isa
TOOLCHAIN_DIR := $(abspath $(ROOT_DIR)/../toolchain)
APPS_DIR := $(ROOT_DIR)
# This will overwrite the ROOT_DIR variable from the included makefile
include $(ROOT_DIR)/common/runtime.mk
include $(TESTS_DIR)/snitch_isa.mk

APPS := $(patsubst $(APPS_DIR)/%/main.c,%,$(shell find $(APPS_DIR) -name "main.c"))
BINARIES := $(addprefix bin/,$(APPS))

# Make all applications
all: $(BINARIES)

$(APPS): % : bin/% $(APPS_DIR)/Makefile $(shell find common -type f)

.PHONY: $(BINARIES)
$(BINARIES): bin/%: %/main.c.o $(RUNTIME) $(LINKER_SCRIPT) update_opcodes
	mkdir -p $(shell dirname $@)
	$(RISCV_CC) -Iinclude $(RISCV_LDFLAGS) -o $@ $< $(RUNTIME) -T$(CURDIR)/common/link.ld
	$(RISCV_OBJDUMP) $(RISCV_OBJDUMP_FLAGS) -D $@ > $@.dump
	$(RISCV_STRIP) $@ -S --strip-unneeded

# Unit tests
TESTS := $(addprefix bin/,$(rtl_mempool_tests))

define rtl_mempool_tests_template

TESTS_$(1) := $(addprefix bin/,$($(1)_mempool_tests))

$$(TESTS_$(1)): bin/$(1)-mempool-%: $(TESTS_DIR)/$(1)/%.S $(LINKER_SCRIPT)
	mkdir -p $$(shell dirname $$@)
	$$(RISCV_CC) $$(RISCV_CCFLAGS_TESTS) -T$$(CURDIR)/common/link.ld $$< -o $$@
	$$(RISCV_STRIP) $$@ -g -S -d --strip-debug
	$$(RISCV_OBJDUMP) $(RISCV_OBJDUMP_FLAGS) -D $$@ > $$@.dump

endef

$(eval $(call rtl_mempool_tests_template,rv32ui))
$(eval $(call rtl_mempool_tests_template,rv32um))
$(eval $(call rtl_mempool_tests_template,rv32ua))
$(eval $(call rtl_mempool_tests_template,rv32uxpulpimg))

test: update_opcodes $(TESTS)

# Helper targets
.PHONY: update_opcodes clean

update_opcodes:
	make -C $(TOOLCHAIN_DIR)/riscv-opcodes all

clean:
	rm -vf $(BINARIES)
	rm -vf $(addsuffix .dump,$(BINARIES))
	rm -vf $(addsuffix /main.c.o,$(APPS))
	rm -vf $(RUNTIME)
	rm -vf $(LINKER_SCRIPT)
	rm -vf $(TESTS)
	rm -vf $(addsuffix .dump,$(TESTS))

.INTERMEDIATE: $(addsuffix /main.c.o,$(APPS))
