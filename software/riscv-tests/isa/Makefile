#=======================================================================
# Makefile for riscv-tests/isa
#-----------------------------------------------------------------------

XLEN ?= 32

src_dir := .

# XLEN 64
ifeq ($(XLEN),64)
	include $(src_dir)/rv64ui/Makefrag
	include $(src_dir)/rv64uc/Makefrag
	include $(src_dir)/rv64um/Makefrag
	include $(src_dir)/rv64ua/Makefrag
	include $(src_dir)/rv64uf/Makefrag
	include $(src_dir)/rv64ud/Makefrag
	ifneq ($(COMPILER), llvm)
	include $(src_dir)/rv64si/Makefrag
	include $(src_dir)/rv64mi/Makefrag
	endif
endif
# XLEN 32
include $(src_dir)/rv32ui/Makefrag
include $(src_dir)/rv32uc/Makefrag
include $(src_dir)/rv32um/Makefrag
include $(src_dir)/rv32ua/Makefrag
include $(src_dir)/rv32uf/Makefrag
include $(src_dir)/rv32ud/Makefrag
ifneq ($(COMPILER), llvm)
include $(src_dir)/rv32si/Makefrag
include $(src_dir)/rv32mi/Makefrag
endif
include $(src_dir)/rv32uxpulpimg/Makefrag

default: all

#--------------------------------------------------------------------
# Build rules
#--------------------------------------------------------------------

MEMPOOL_DIR       := $(shell git rev-parse --show-toplevel 2>/dev/null || echo $$MEMPOOL_DIR)
INSTALL_DIR       ?= $(MEMPOOL_DIR)/install
GCC_INSTALL_DIR   ?= $(INSTALL_DIR)/riscv-gcc
LLVM_INSTALL_DIR  ?= $(INSTALL_DIR)/llvm
SPIKE_INSTALL_DIR ?= $(INSTALL_DIR)/riscv-isa-sim
RISCV_SIM 				?= $(SPIKE_INSTALL_DIR)/bin/spike


ifeq ($(COMPILER), llvm)
	RISCV_PREFIX ?= $(LLVM_INSTALL_DIR)/bin/llvm-
	RISCV_CC ?= $(LLVM_INSTALL_DIR)/bin/clang
	RISCV_TARGET ?= riscv$(XLEN)-unknown-elf
	RISCV_LLVM_TARGET  ?= --target=$(RISCV_TARGET) --sysroot=$(GCC_INSTALL_DIR)/$(RISCV_TARGET) --gcc-toolchain=$(GCC_INSTALL_DIR)
	RISCV_CC_OPTS ?= -static -mcmodel=medany -fvisibility=hidden -nostdlib -nostartfiles $(RISCV_LLVM_TARGET)
	RISCV_OBJDUMP_FLAGS += --mattr=+m,+a,+xpulpmacsi,+xpulppostmod,+xpulpvect,+xpulpvectshufflepack,+f
	RISCV_OBJDUMP ?= $(RISCV_PREFIX)objdump $(RISCV_OBJDUMP_FLAGS) --disassemble-all --disassemble-zeroes --section=.text --section=.text.startup --section=.text.init --section=.data
else
	# Default compilation with GCC
	RISCV_PREFIX ?= $(GCC_INSTALL_DIR)/bin/riscv$(XLEN)-unknown-elf-
	RISCV_CC ?= $(RISCV_PREFIX)gcc
	RISCV_CC_OPTS ?= -static -mcmodel=medany -fvisibility=hidden -nostdlib -nostartfiles
	RISCV_OBJDUMP ?= $(RISCV_PREFIX)objdump --disassembler-option="march=rv32gXpulpimg" --disassemble-all --disassemble-zeroes --section=.text --section=.text.startup --section=.text.init --section=.data
endif


vpath %.S $(src_dir)

#------------------------------------------------------------
# Build assembly tests

%.dump: %
	$(RISCV_OBJDUMP) $< > $@

%.out: %
	PATH="$(MEMPOOL_DIR)/install/riscv-isa-sim/bin:$$PATH"; \
	$(RISCV_SIM) --isa=rv64gc $< 2> $@

%.out32: %
	PATH="$(MEMPOOL_DIR)/install/riscv-isa-sim/bin:$$PATH"; \
	$(RISCV_SIM) --isa=rv32gc $< 2> $@

ifeq ($(COMPILER), llvm)

define compile_template
$$($(1)_p_tests): $(1)-p-%: $(1)/%.S
	$$(RISCV_CC) $(2) $$(RISCV_CC_OPTS) -DLLVM -I$(src_dir)/../env/p -I$(src_dir)/macros/scalar -T$(src_dir)/../env/p/link.ld $$< -o $$@
$(1)_tests += $$($(1)_p_tests)

$(1)_tests_dump = $$(addsuffix .dump, $$($(1)_tests))
$(1): $$($(1)_tests_dump)

.PHONY: $(1)
tests += $$($(1)_tests)
endef

else

define compile_template
$$($(1)_p_tests): $(1)-p-%: $(1)/%.S
	$$(RISCV_CC) $(2) $$(RISCV_CC_OPTS) -I$(src_dir)/../env/p -I$(src_dir)/macros/scalar -T$(src_dir)/../env/p/link.ld $$< -o $$@
$(1)_tests += $$($(1)_p_tests)

$$($(1)_v_tests): $(1)-v-%: $(1)/%.S
	$$(RISCV_CC) $(2) $$(RISCV_CC_OPTS) -DENTROPY=0x$$(shell echo \$$@ | md5sum | cut -c 1-7) -std=gnu99 -O2 -I$(src_dir)/../env/v -I$(src_dir)/macros/scalar -T$(src_dir)/../env/v/link.ld $(src_dir)/../env/v/entry.S $(src_dir)/../env/v/*.c $$< -o $$@
$(1)_tests += $$($(1)_v_tests)

$(1)_tests_dump = $$(addsuffix .dump, $$($(1)_tests))
$(1): $$($(1)_tests_dump)

.PHONY: $(1)
tests += $$($(1)_tests)
endef

endif

# Single precision

# Xpulpimg
ifeq ($(COMPILER),llvm)
$(eval $(call compile_template,rv32ui,-march=rv32g -mabi=ilp32))
$(eval $(call compile_template,rv32uc,-march=rv32g -mabi=ilp32))
$(eval $(call compile_template,rv32um,-march=rv32g -mabi=ilp32))
$(eval $(call compile_template,rv32ua,-march=rv32g -mabi=ilp32))
$(eval $(call compile_template,rv32uf,-march=rv32g -mabi=ilp32))
$(eval $(call compile_template,rv32ud,-march=rv32g -mabi=ilp32))
RISCV_ARCH ?= rv$(XLEN)ima_xpulppostmod_xpulpmacsi_xpulpvect_xpulpvectshufflepack_xmempool
$(eval $(call compile_template,rv32uxpulpimg,-march=$(RISCV_ARCH) -mabi=ilp32))
else
$(eval $(call compile_template,rv32ui,-march=rv32g -mabi=ilp32))
$(eval $(call compile_template,rv32uc,-march=rv32g -mabi=ilp32))
$(eval $(call compile_template,rv32um,-march=rv32g -mabi=ilp32))
$(eval $(call compile_template,rv32ua,-march=rv32g -mabi=ilp32))
$(eval $(call compile_template,rv32uf,-march=rv32g -mabi=ilp32))
$(eval $(call compile_template,rv32ud,-march=rv32g -mabi=ilp32))
$(eval $(call compile_template,rv32si,-march=rv32g -mabi=ilp32))
$(eval $(call compile_template,rv32mi,-march=rv32g -mabi=ilp32))
$(eval $(call compile_template,rv32uxpulpimg,-march=rv32gXpulpimg -mabi=ilp32))
endif

# Double precision
ifeq ($(XLEN),64)
$(eval $(call compile_template,rv64ui,-march=rv64g -mabi=lp64))
$(eval $(call compile_template,rv64uc,-march=rv64g -mabi=lp64))
$(eval $(call compile_template,rv64um,-march=rv64g -mabi=lp64))
$(eval $(call compile_template,rv64ua,-march=rv64g -mabi=lp64))
$(eval $(call compile_template,rv64uf,-march=rv64g -mabi=lp64))
$(eval $(call compile_template,rv64ud,-march=rv64g -mabi=lp64))
$(eval $(call compile_template,rv64si,-march=rv64g -mabi=lp64))
$(eval $(call compile_template,rv64mi,-march=rv64g -mabi=lp64))
endif

tests_dump = $(addsuffix .dump, $(tests))
tests_hex = $(addsuffix .hex, $(tests))
tests_out = $(addsuffix .out, $(spike_tests))
tests32_out = $(addsuffix .out32, $(spike32_tests))

run: $(tests_out) $(tests32_out)

junk += $(tests) $(tests_dump) $(tests_hex) $(tests_out) $(tests32_out)

#------------------------------------------------------------
# Default

all: $(tests_dump)

#------------------------------------------------------------
# Clean up

clean:
	rm -rf $(junk)
