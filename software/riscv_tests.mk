# Copyright 2021 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Unit tests
RISCV_TESTS := $(addprefix bin/,$(rtl_tests))

define rtl_mempool_tests_template

bin/$(1)-%.o: $(RISCV_TESTS_DIR)/$(1)/%.S
	mkdir -p $$(shell dirname $$@)
	$$(RISCV_CC) $$(RISCV_CCFLAGS) -c $$< -o $$@

bin/$(1)-%: bin/$(1)-%.o $(LINKER_SCRIPT)
	mkdir -p $$(shell dirname $$@)
	$$(RISCV_CC) $$(RISCV_LDFLAGS) -o $$@ $$< -T$$(RUNTIME_DIR)/link.ld
	$$(RISCV_STRIP) $$@ -g -S -d --strip-debug
	$$(RISCV_OBJDUMP) $(RISCV_OBJDUMP_FLAGS) -D $$@ > $$@.dump
endef

$(foreach suite,rv32ui rv32ua rv32um rv32uxpulpimg rv32uzfinx rv32uzhinx rv32uxsmallfloathinx rv32uxsmallfloatbinx,$(eval $(call rtl_mempool_tests_template,$(suite))))

riscv-tests: update-opcodes $(RISCV_TESTS)

clean-riscv-test:
	rm -vf $(RUNTIME)
	rm -vf $(LINKER_SCRIPT)
	rm -vf $(RISCV_TESTS)
	rm -vf $(addsuffix .o,$(RISCV_TESTS))
	rm -vf $(addsuffix .pp.s,$(RISCV_TESTS))
	rm -vf $(addsuffix .dump,$(RISCV_TESTS))
