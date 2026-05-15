# Copyright 2021 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Unit tests
RISCV_TESTS := $(addprefix bin/,$(rtl_mempool_tests))

ifeq ($(COMPILER), llvm)
RISCV_TESTS_LLVM_MATTR := +m,+a,+zfinx,+zhinx
RISCV_TESTS_LLVM_MATTR := $(RISCV_TESTS_LLVM_MATTR),$(call comma-join,$(addprefix +,$(XPULPIMG_FEATURES)))
RISCV_TESTS_LLVM_MATTR := $(RISCV_TESTS_LLVM_MATTR),$(call comma-join,$(addprefix +,$(ZFINX_FEATURES)))
RISCV_TESTS_LLVM_MATTR := $(RISCV_TESTS_LLVM_MATTR)$(if $(XDIVSQRT),,+nofdiv)
endif

define rtl_mempool_tests_template

RISCV_TESTS_$(1) := $(addprefix bin/,$($(1)_mempool_tests))

bin/$(1)-mempool-%.o: $(RISCV_TESTS_DIR)/$(1)/%.S
	mkdir -p $$(shell dirname $$@)
	$$(RISCV_CC) $$(RISCV_CCFLAGS) -c $$< -o $$@

bin/$(1)-mempool-%: bin/$(1)-mempool-%.o $(LINKER_SCRIPT)
	mkdir -p $$(shell dirname $$@)
	$$(RISCV_CC) $$(RISCV_LDFLAGS) -o $$@ $$< -T$$(RUNTIME_DIR)/link.ld
	$$(RISCV_STRIP) $$@ -g -S -d --strip-debug
	$$(RISCV_OBJDUMP) $(RISCV_OBJDUMP_FLAGS) -D $$@ > $$@.dump
endef


ifeq ($(COMPILER), llvm)
$(eval $(call rtl_mempool_tests_template,rv32ui))
$(eval $(call rtl_mempool_tests_template,rv32um))
$(eval $(call rtl_mempool_tests_template,rv32ua))
$(eval $(call rtl_mempool_tests_template,rv32uzfinx))
$(eval $(call rtl_mempool_tests_template,rv32uzhinx))
$(eval $(call rtl_mempool_tests_template,rv32uxpulpimg))
$(eval $(call rtl_mempool_tests_template,rv32uxsmallfloathinx))
$(eval $(call rtl_mempool_tests_template,rv32uxsmallfloatbinx))
else
$(eval $(call rtl_mempool_tests_template,rv32ui))
$(eval $(call rtl_mempool_tests_template,rv32um))
$(eval $(call rtl_mempool_tests_template,rv32ua))
$(eval $(call rtl_mempool_tests_template,rv32uxpulpimg))
endif

riscv-tests: update-opcodes $(RISCV_TESTS)

clean-riscv-test:
	rm -vf $(RUNTIME)
	rm -vf $(LINKER_SCRIPT)
	rm -vf $(RISCV_TESTS)
	rm -vf $(addsuffix .o,$(RISCV_TESTS))
	rm -vf $(addsuffix .pp.s,$(RISCV_TESTS))
	rm -vf $(addsuffix .dump,$(RISCV_TESTS))
