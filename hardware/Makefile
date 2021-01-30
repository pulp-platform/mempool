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
MEMPOOL_DIR := $(shell git rev-parse --show-toplevel 2>/dev/null || echo $$MEMPOOL_DIR)
INSTALL_DIR := $(abspath $(ROOT_DIR)/../install)
TOOLCHAIN_DIR := $(abspath $(ROOT_DIR)/../toolchain)

# Include configuration
config_mk = $(abspath $(ROOT_DIR)/../config/config.mk)
include $(config_mk)

# build path
buildpath      ?= build
resultpath     ?= results
# questa library
library        ?= work
# dpi library
dpi_library    ?= work-dpi
# Top level module to compile
top_level      ?= mempool_tb
# QuestaSim Version
questa_version ?= 2019.3
# QuestaSim command
questa_cmd     ?= questa-$(questa_version)
# QuestaSim arguments
questa_args    ?=
# Path to the binaries
app_path       ?= $(abspath $(ROOT_DIR)/../apps/bin)
# Bender
bender         ?= $(INSTALL_DIR)/bender/bender
# Verilator
verilator      ?= $(INSTALL_DIR)/verilator/bin/verilator
# Python
python         ?= python3.6

# Check if the specified QuestaSim version exists
ifeq (, $(shell which $(questa_cmd)))
  # Spaces are needed for indentation here!
  $(warning "Specified QuestaSim version ($(questa_cmd)) not found in PATH $(PATH)")
  questa_cmd =
endif

QUESTASIM_HOME ?= /usr/pack/questa-$(questa_version)-kgf/questasim

questa_args += -voptargs=+acc
ifdef app
	preload ?= "$(app_path)/$(app)"
endif
ifdef preload
	questa_args += +PRELOAD=$(preload)
endif
questa_args += -sv_lib $(dpi_library)/mempool_dpi -work $(library)
questa_args += -suppress vsim-12070

# DPI source files
dpi   := $(patsubst tb/dpi/%.cpp,$(buildpath)/$(dpi_library)/%.o,$(wildcard tb/dpi/*.cpp))
# Traces
trace = $(patsubst $(buildpath)/%.dasm,$(buildpath)/%.trace,$(wildcard $(buildpath)/*.dasm))
tracepath ?= $(buildpath)/traces
traceresult ?= $(tracepath)/results.csv
ifndef result_dir
	result_dir := $(resultpath)/$(shell date +"%Y%m%d_%H%M%S_$(app)_$$(git rev-parse --short HEAD)")
endif

vlog_args += -suppress vlog-2583 -suppress vlog-13314 -suppress vlog-13233
vlog_args += -work $(library)
# Defines
vlog_defs += -DNUM_CORES=$(num_cores) -DNUM_CORES_PER_TILE=$(num_cores_per_tile)
vlog_defs += -DL2_BASE="32'h$(l2_base)" -DL2_SIZE="32'h$(l2_size)"
vlog_defs += -DBOOT_ADDR="32'h$(boot_addr)" -DXPULPIMG="1'b$(xpulpimg)"

cpp_defs  += -DL2_BASE=0x$(l2_base) -DL2_SIZE=0x$(l2_size)

.DEFAULT_GOAL := compile

# Build path
$(buildpath):
	mkdir -p $(buildpath)

# Bender
$(bender):
	make -C $(MEMPOOL_DIR) bender

################
# Modelsim
################
# Library
.PHONY: lib
lib: $(buildpath) $(buildpath)/$(library)
$(buildpath)/$(library):
	cd $(buildpath) && $(questa_cmd) vlib $(library) && chmod +w modelsim.ini; $(questa_cmd) vmap $(library) $(library)

# Compilation
.PHONY: compile
compile: dpi lib $(buildpath) $(buildpath)/compile.tcl update_opcodes
$(buildpath)/compile.tcl: $(bender) $(config_mk) Makefile $(MEMPOOL_DIR)/Bender.yml $(shell find {src,tb,deps} -type f)
	$(bender) script vsim --vlog-arg="$(vlog_args)" $(vlog_defs) -t rtl -t mempool_vsim > $(buildpath)/compile.tcl
	echo "exit" >> $(buildpath)/compile.tcl
	cd $(buildpath) && $(questa_cmd) vsim -work $(library) -c -do compile.tcl

# Simulation
.PHONY: sim
sim: clean-dasm compile
	cd $(buildpath) && \
	$(questa_cmd) vsim $(questa_args) $(library).$(top_level) -do ../scripts/run.do
	./scripts/return_status.sh $(buildpath)/transcript

.PHONY: simc
simc: clean-dasm compile
	cd $(buildpath) && \
	$(questa_cmd) vsim -c $(questa_args) $(library).$(top_level) -do "run -a"
	./scripts/return_status.sh $(buildpath)/transcript

# Unit tests simulation
TESTS_DIR := $(abspath $(ROOT_DIR)/../apps/riscv-tests/isa)
include $(TESTS_DIR)/snitch_isa.mk

test_result_dir := $(resultpath)/test_result

tests := $(addsuffix .out,$(addprefix $(test_result_dir)/,$(rtl_mempool_tests)))

simc_test: clean-dasm compile $(tests)

$(tests): $(test_result_dir)/%.out : $(app_path)/%
	mkdir -p $(test_result_dir)
	cd $(buildpath) && \
	$(questa_cmd) vsim -c $(questa_args) +PRELOAD=$< $(library).$(top_level) -do "run -a"
	./scripts/return_status.sh $(buildpath)/transcript > $@

################
# Verilator
################
VERILATOR_DIR    = $(ROOT_DIR)/verilator
VERILATOR_BUILD  = $(ROOT_DIR)/obj_dir
VERILATOR_FILES  = $(VERILATOR_BUILD)/files
VERILATOR_LIBS  := $(shell find $(VERILATOR_DIR) -name "*.cc" -print | sort)
VERILATOR_INCS  := $(shell find $(VERILATOR_DIR) -name "cpp" -print | sort)
VERILATOR_TOP   := mempool_tb_verilator
VERILATOR_BIN   := $(VERILATOR_BUILD)/V$(VERILATOR_TOP)
VERILATOR_MK    := $(VERILATOR_BIN).mk
VERILATOR_WAIVE := $(shell find $(VERILATOR_DIR) -name "*.vlt" -print | sort)
VERILATOR_CONF  := $(VERILATOR_DIR)/verilator.flags

# VERILATOR_FLAGS += --trace --trace-fst --trace-structs --trace-params --trace-max-array 1024
# VERILATOR_FLAGS += --debug

VERILATOR_FLAGS += -CFLAGS "-DTOPLEVEL_NAME=$(VERILATOR_TOP)"
VERILATOR_FLAGS += --Mdir $(VERILATOR_BUILD)
VERILATOR_FLAGS += -f $(VERILATOR_FILES)
VERILATOR_FLAGS += -f $(VERILATOR_CONF)
VERILATOR_FLAGS += $(VERILATOR_WAIVE)

$(VERILATOR_MK): $(VERILATOR_CONF) $(VERILATOR_WAIVE) $(MEMPOOL_DIR)/Bender.yml $(shell find {src,tb,deps} -type f) $(bender) $(config_mk) Makefile
	mkdir -p $(VERILATOR_BUILD)
	# Create Bender script of all RTL files
	$(bender) script verilator $(vlog_defs) -t rtl -t mempool_verilator > $(VERILATOR_FILES)
	# Append the verilator library files
	@echo '' >> $(VERILATOR_FILES)
	# Append the verilator library files: Includes
	@echo $(addprefix +incdir+,$(VERILATOR_INCS)) | tr ' ' '\n' >> $(VERILATOR_FILES)
	for i in $(VERILATOR_INCS); do echo "-CFLAGS -I$${i}" >> $(VERILATOR_FILES); done
	# Append the CPP defines
	@echo "-CFLAGS \"$(cpp_defs)\"" >> $(VERILATOR_FILES)
	# Append the verilator library files: source files
	@echo $(VERILATOR_LIBS) | tr ' ' '\n'  >> $(VERILATOR_FILES)
	# Create Verilator Makefile
	$(verilator) $(VERILATOR_FLAGS) --top-module $(VERILATOR_TOP)

$(VERILATOR_BIN): $(VERILATOR_MK) $(shell find $(VERILATOR_DIR) -type f) Makefile
	make -j4 -C $(VERILATOR_BUILD) -f $<

verilate: $(VERILATOR_BIN) Makefile
	$(VERILATOR_BIN) --meminit=ram,$(preload)

# Benchmarking
benchmark: log simc
	# Call `make` again to get variable extension with all traces
	result_dir=$(result_dir) $(MAKE) trace

trace: pre_trace $(trace) post_trace

log:
	mkdir -p "$(result_dir)"
	[ -e "$(preload)" ] && cp "$(preload)"* "$(result_dir)" || \
	([ -e "$(buildpath)/transcript" ] && \
	cp "$$(grep -oP '(?<=\+PRELOAD=)[^ \"]*' $(buildpath)/transcript)"* "$(result_dir)" || \
	echo "No application specified")
	env > "$(result_dir)/env"
	cp $(MEMPOOL_DIR)/config/config.mk $(result_dir)/config
	git rev-parse HEAD > "$(result_dir)/git-info.diff"
	git show --oneline -s >> "$(result_dir)/git-info.diff"
	git diff >> "$(result_dir)/git-info.diff"

pre_trace:
	rm -rf $(tracepath)

post_trace:
	mkdir -p "$(result_dir)"
	cp $(buildpath)/transcript "$(result_dir)/"
	cp $(traceresult) "$(result_dir)"
	cp $(trace) "$(result_dir)"

$(buildpath)/%.trace: $(buildpath)/%.dasm
	mkdir -p $(tracepath)
	$(INSTALL_DIR)/riscv-isa-sim/bin/spike-dasm < $< > $(tracepath)/$*
	$(python) $(ROOT_DIR)/deps/snitch/scripts/gen_trace.py --csv $(traceresult) $(tracepath)/$* > $@

# DPIs
.PHONY: dpi
dpi: $(buildpath)/$(dpi_library)/mempool_dpi.so

$(buildpath)/$(dpi_library)/%.o: tb/dpi/%.cpp
	mkdir -p $(buildpath)/$(dpi_library)
	$(CXX) -shared -fPIC -std=c++11 -Bsymbolic -c $< -I$(QUESTASIM_HOME)/include -o $@

$(buildpath)/$(dpi_library)/mempool_dpi.so: $(dpi)
	mkdir -p $(buildpath)/$(dpi_library)
	$(CXX) -shared -m64 -o $(buildpath)/$(dpi_library)/mempool_dpi.so $?

# Bootrom
src/bootrom.sv: $(MEMPOOL_DIR)/apps/common/bootrom.img
	$(python) ./scripts/generate_bootrom.py --sv --output src/bootrom --datawidth 128 $<

$(MEMPOOL_DIR)/apps/common/bootrom.img:
	make -C $(MEMPOOL_DIR)/apps common/bootrom.img

# Clean targets
.PHONY: clean clean-dasm clean-trace update_opcodes

update_opcodes:
	make -C $(TOOLCHAIN_DIR)/riscv-opcodes all

clean:
	rm -rf $(buildpath)

clean-dasm:
	rm -rf $(buildpath)/*.dasm

clean-trace:
	rm -rf $(buildpath)/*.trace
