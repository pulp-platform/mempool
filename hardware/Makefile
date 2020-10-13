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
questa_version ?= 2020.1
# QuestaSim command
questa_cmd     ?= questa-$(questa_version)
# QuestaSim arguments
questa_args    ?=
# Path to the binaries
app_path       ?= $(abspath $(ROOT_DIR)/../apps/bin)

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
vlog_args += +define+NUM_CORES=$(num_cores) +define+NUM_CORES_PER_TILE=$(num_cores_per_tile) +define+BOOT_ADDR=32'h$(boot_addr)

# Build path
$(buildpath):
	mkdir -p $(buildpath)

# Bender
bender:
	@[ -x ./bender ] && echo "Bender already exists." || \
	(command -v bender >/dev/null 2>&1 && ln -sf $$(command -v bender) ./bender || \
	curl --proto '=https' --tlsv1.2 -sSf https://iis-people.ee.ethz.ch/~andkurt/bender-init \
		| bash -s -- 0.19.0)
	@touch bender
	@echo "$$(./bender --version) available."

# Library
.PHONY: lib
lib: $(buildpath) $(buildpath)/$(library)
$(buildpath)/$(library):
	cd $(buildpath) && $(questa_cmd) vlib $(library) && $(questa_cmd) vmap $(library) $(library)

# Compilation
.PHONY: compile
compile: dpi lib $(buildpath) $(buildpath)/compile.tcl
$(buildpath)/compile.tcl: bender $(config_mk) $(shell find src -type f) $(shell find tb -type f) $(shell find deps -type f)
	./bender script vsim --vlog-arg="$(vlog_args)" -t rtl -t asic -t mempool_test > $(buildpath)/compile.tcl
	echo "exit" >> $(buildpath)/compile.tcl
	cd $(buildpath) && $(questa_cmd) vsim -work $(library) -c -do compile.tcl

# Simulation
.PHONY: sim
sim: compile
	cd $(buildpath) && \
	$(questa_cmd) vsim $(questa_args) $(library).$(top_level) -do ../scripts/run.do
	./scripts/return_status.sh $(buildpath)/transcript

.PHONY: simc
simc: compile
	cd $(buildpath) && \
	$(questa_cmd) vsim -c $(questa_args) $(library).$(top_level) -do "run -a"
	./scripts/return_status.sh $(buildpath)/transcript

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

# Clean targets
.PHONY: clean clean-dasm clean-trace
clean:
	rm -rf $(buildpath)

clean-dasm:
	rm -rf $(buildpath)/*.dasm

clean-trace:
	rm -rf $(buildpath)/*.trace
