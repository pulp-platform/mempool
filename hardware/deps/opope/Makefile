# Copyright 2025 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Danilo Cammarata <dcammarata@iis.ee.ethz.ch>
#
# Top-level Makefile

# Paths to folders
RootDir    := $(dir $(abspath $(firstword $(MAKEFILE_LIST))))
TargetDir  := $(RootDir)target
SimDir     := $(TargetDir)/sim
ScriptsDir := $(RootDir)scripts
VerilatorPath := target/sim/verilator
VsimPath      := target/sim/vsim
SW         ?= $(RootDir)sw
BUILD_DIR  ?= $(SW)/build
SIM_DIR    ?= $(RootDir)vsim
QUESTA     ?= questa-2023.4
Bender     ?= $(CargoInstallDir)/bin/bender
Gcc        ?= $(GccInstallDir)/bin/
ISA        ?= riscv
ARCH       ?= rv
XLEN       ?= 32
XTEN       ?= imc_zicsr
PYTHON     ?= python3

target ?= vsim
TargetPath := $(SimDir)/$(target)

# Included makefrags
include $(TargetPath)/$(target).mk
include bender_common.mk
include bender_sim.mk
include bender_synth.mk

ifeq ($(OPOPE_COMPLEX),1)
	TEST_SRCS := $(SW)/opope_complex.c
else
	TEST_SRCS := $(SW)/opope.c
endif

compile_script_synth ?= $(RootDir)scripts/synth_compile.tcl

WORK_PATH = $(SIM_DIR)/work

# Useful Parameters
gui      ?= 0
ipstools ?= 0
P_STALL  ?= 0.0

DEBUG ?= 1

ifeq ($(verbose),1)
	FLAGS += -DVERBOSE
endif

ifeq ($(debug),1)
	FLAGS += -DDEBUG
endif



# endif

# Include directories
INC += -I$(SW)
INC += -I$(SW)/inc
INC += -I$(SW)/utils

BOOTSCRIPT := $(SW)/kernel/crt0.S
LINKSCRIPT := $(SW)/kernel/link.ld

CC=$(Gcc)$(ISA)$(XLEN)-unknown-elf-gcc
LD=$(CC)
OBJDUMP=$(Gcc)$(ISA)$(XLEN)-unknown-elf-objdump
CC_OPTS=-march=$(ARCH)$(XLEN)$(XTEN) -mabi=ilp32 -D__$(ISA)__ -O2 -g -Wextra -Wall -Wno-unused-parameter -Wno-unused-variable -Wno-unused-function -Wundef -fdata-sections -ffunction-sections -MMD -MP -Wincompatible-pointer-types -Wimplicit-fallthrough
LD_OPTS=-march=$(ARCH)$(XLEN)$(XTEN) -mabi=ilp32 -D__$(ISA)__ -MMD -MP -nostartfiles -nostdlib -Wl,--gc-sections

# Setup build object dirs
CRT=$(BUILD_DIR)/crt0.o
OBJ=$(BUILD_DIR)/verif.o
BIN=$(BUILD_DIR)/verif
DUMP=$(BUILD_DIR)/verif.dump
STIM_INSTR=$(BUILD_DIR)/stim_instr.txt
STIM_DATA=$(BUILD_DIR)/stim_data.txt

# Build implicit rules
$(STIM_INSTR) $(STIM_DATA): $(BIN)
	objcopy --srec-len 1 --output-target=srec $(BIN) $(BIN).s19
	$(PYTHON) scripts/parse_s19.py < $(BIN).s19 > $(BIN).txt
	$(PYTHON) scripts/s19tomem.py $(BIN).txt $(STIM_INSTR) $(STIM_DATA)

$(BIN): $(CRT) $(OBJ)
	$(LD) $(LD_OPTS) -o $(BIN) $(CRT) $(OBJ) -T$(LINKSCRIPT)

$(CRT): $(BUILD_DIR)
	$(CC) $(CC_OPTS) -c $(BOOTSCRIPT) -o $(CRT)

$(OBJ): $(TEST_SRCS)
	$(CC) $(CC_OPTS) -c $(TEST_SRCS) $(FLAGS) $(INC) -o $(OBJ)

$(BUILD_DIR):
	mkdir -p $(BUILD_DIR)

SHELL := /bin/bash

init: riscv32-gcc bender
	source scripts/setup-py.sh
	
init-iis:
	ln -s /usr/scratch2/larain3/dcammarata/opope/golden-model/venv golden-model/venv
	ln -s /usr/scratch2/larain3/dcammarata/opope/vendor vendor 

# Generate instructions and data stimuli
sw-build: $(STIM_INSTR) $(STIM_DATA_X_W) $(STIM_DATA_Y_Z) dis

$(SIM_DIR):
	mkdir -p $(SIM_DIR)

synth-ips:
	$(Bender) update
	$(Bender) script synopsys      \
	$(common_targs) $(common_defs) \
	$(synth_targs) $(synth_defs)   \
	> ${compile_script_synth}

sw-clean:
	rm -rf $(BUILD_DIR)

dis:
	$(OBJDUMP) -d $(BIN) > $(DUMP)

OP     ?= gemm
fp_fmt ?= FP16
M      ?= 4
N      ?= 4
K      ?= 4
transpose ?= 1

golden: golden-clean
	$(MAKE) -C golden-model $(OP) SW=$(SW)/inc M=$(M) N=$(N) K=$(K) fp_fmt=$(fp_fmt) transpose=$(transpose)

golden-clean:
	$(MAKE) -C golden-model golden-clean

clean-all: sw-clean
	rm -rf $(RootDir).bender
	rm -rf $(compile_script)

sw-all: sw-clean sw-build

sim: hw-clean sw-clean synth-ips hw-script hw-build sw-build hw-run

sim-all:
	mkdir -p logs
	rm -rf logs/*
	source scripts/run_all.sh &> logs/sim_all.log

# Install tools
CXX ?= g++
NumCores := $(shell nproc)
NumCoresHalf := $(shell echo "$$(($(NumCores) / 2))")
VendorDir ?= $(RootDir)vendor
InstallDir ?= $(VendorDir)/install
# Verilator
VerilatorVersion ?= v5.028
VerilatorInstallDir := $(InstallDir)/verilator
# GCC
GccInstallDir := $(InstallDir)/riscv
RiscvTarDir := riscv.tar.gz
GccUrl := https://github.com/riscv-collab/riscv-gnu-toolchain/releases/download/2024.08.28/riscv32-elf-ubuntu-20.04-gcc-nightly-2024.08.28-nightly.tar.gz
# Bender
RustupInit := $(ScriptsDir)/rustup-init.sh
CargoInstallDir := $(InstallDir)/cargo
RustupInstallDir := $(InstallDir)/rustup
Cargo := $(CargoInstallDir)/bin/cargo

verilator: $(InstallDir)/bin/verilator

$(InstallDir)/bin/verilator:
	rm -rf $(VendorDir)/verilator
	mkdir -p $(VendorDir) && cd $(VendorDir) && git clone https://github.com/verilator/verilator.git
	# Checkout the right version
	cd $(VendorDir)/verilator && git reset --hard && git fetch && git checkout $(VerilatorVersion)
	# Compile verilator
	sudo apt install libfl-dev help2man
	mkdir -p $(VerilatorInstallDir) && cd $(VendorDir)/verilator && git clean -xfdf && autoconf && \
	./configure --prefix=$(VerilatorInstallDir) CXX=$(CXX) && make -j$(NumCoresHalf)  && make install

riscv32-gcc: $(GccInstallDir)

$(GccInstallDir):
	rm -rf $(GccInstallDir) $(VendorDir)/$(RiscvTarDir)
	mkdir -p $(InstallDir)
	cd $(VendorDir) && \
	wget $(GccUrl) -O $(RiscvTarDir) && \
	tar -xzvf $(RiscvTarDir) -C $(InstallDir) riscv

bender: $(CargoInstallDir)/bin/bender

$(CargoInstallDir)/bin/bender:
	curl --proto '=https' --tlsv1.2 https://sh.rustup.rs -sSf > $(RustupInit)
	mkdir -p $(InstallDir)
	export CARGO_HOME=$(CargoInstallDir) && export RUSTUP_HOME=$(RustupInstallDir) && \
	chmod +x $(RustupInit); source $(RustupInit) -y && \
	$(Cargo) install bender
	rm -rf $(RustupInit)
