INSTALL_DIR        ?= ../install
GCC_INSTALL_DIR    ?= $(INSTALL_DIR)/riscv-gcc
LLVM_INSTALL_DIR   ?= $(INSTALL_DIR)/llvm
HALIDE_INSTALL_DIR ?= $(INSTALL_DIR)/halide

RISCV_XLEN    ?= 32
RISCV_ARCH    ?= rv$(RISCV_XLEN)im
RISCV_ABI     ?= ilp32
RISCV_PREFIX  ?= $(GCC_INSTALL_DIR)/bin/riscv$(RISCV_XLEN)-unknown-elf-
RISCV_CC      ?= $(RISCV_PREFIX)gcc
RISCV_CXX     ?= $(RISCV_PREFIX)g++
RISCV_OBJDUMP ?= $(RISCV_PREFIX)objdump
RISCV_OBJCOPY ?= $(RISCV_PREFIX)objcopy
RISCV_AS      ?= $(RISCV_PREFIX)as
RISCV_AR      ?= $(RISCV_PREFIX)ar
RISCV_LD      ?= $(RISCV_PREFIX)ld
RISCV_STRIP   ?= $(RISCV_PREFIX)strip

RISCV_FLAGS    ?= -march=$(RISCV_ARCH) -mabi=$(RISCV_ABI) -I$(CURDIR)/common -DITERATIONS=10 -mcmodel=medany -static -std=gnu99 -O3 -ffast-math -fno-common -fno-builtin-printf
RISCV_CCFLAGS  ?= $(RISCV_FLAGS)
RISCV_CXXFLAGS ?= $(RISCV_FLAGS)
RISCV_LDFLAGS  ?= -static -nostartfiles -lm -lgcc $(RISCV_FLAGS)

RUNTIME ?= common/crt0.S.o common/printf.c.o common/string.c.o common/serial.c.o common/arch.ld
HDR ?=     common/runtime.h

%.S.o: %.S
	$(RISCV_CC) -Iinclude $(RISCV_CCFLAGS) -c $< -o $@

%.c.o: %.c
	$(RISCV_CC) -Iinclude $(RISCV_CCFLAGS) -c $< -o $@

%.cpp.o: %.cpp
	$(RISCV_CXX) $(RISCV_CXXFLAGS) -c $< -o $@
