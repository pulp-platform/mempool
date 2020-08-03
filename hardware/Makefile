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

ROOT_DIR := $(patsubst %/,%, $(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
INSTALL_DIR := $(abspath $(ROOT_DIR)/../install)
SHELL = /usr/bin/env bash

# build path
buildpath      ?= build
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
questa_args += -sv_lib ${dpi_library}/mempool_dpi

# DPI source files
dpi   := $(patsubst tb/dpi/%.cpp,${buildpath}/${dpi_library}/%.o,$(wildcard tb/dpi/*.cpp))
trace := $(patsubst ${buildpath}/%.dasm,${buildpath}/%.trace,$(wildcard ${buildpath}/*.dasm))

VLOG_ARGS += -suppress vlog-2583 -suppress vlog-13314 -suppress vlog-13233

build: bender lib ${buildpath}/${dpi_library}/mempool_dpi.so
	./bender script vsim --vlog-arg="$(VLOG_ARGS)" -t rtl -t asic -t mempool_test > ${buildpath}/compile.tcl
	echo "exit" >> ${buildpath}/compile.tcl
	cd ${buildpath} && $(questa_cmd) vsim -c -do compile.tcl

lib:
	mkdir -p ${buildpath}
	mkdir -p ${buildpath}/${library}
	cd ${buildpath} && $(questa_cmd) vlib work && $(questa_cmd) vmap work work

sim: build
	cd ${buildpath} && $(questa_cmd) vsim $(questa_args) ${library}.${top_level}

simc: build
	cd ${buildpath} && $(questa_cmd) vsim -c $(questa_args) ${library}.${top_level}

run: build
	cd ${buildpath} && $(questa_cmd) vsim $(questa_args) ${library}.${top_level} -do ../scripts/run.do
	./scripts/return_status.sh ${buildpath}/transcript

trace: $(trace)

${buildpath}/%.trace: ${buildpath}/%.dasm
	mkdir -p ${buildpath}
	$(INSTALL_DIR)/riscv-isa-sim/bin/spike-dasm < $< > $(buildpath)/tmp
	$(python) $(ROOT_DIR)/deps/snitch/scripts/gen_trace.py $(buildpath)/tmp > $@

# Bender
bender: Makefile
	@[ -x ./bender ] && echo "Bender already exists." || \
	(command -v bender >/dev/null 2>&1 && ln -sf $$(command -v bender) ./bender || \
	curl --proto '=https' --tlsv1.2 -sSf https://iis-people.ee.ethz.ch/~andkurt/bender-init \
		| bash -s -- 0.19.0)
	@touch bender
	@echo "$$(./bender --version) available."

# DPIs
${buildpath}/${dpi_library}/%.o: tb/dpi/%.cpp
	mkdir -p ${buildpath}/${dpi_library}
	$(CXX) -shared -fPIC -std=c++11 -Bsymbolic -c $< -I${QUESTASIM_HOME}/include -o $@

${buildpath}/${dpi_library}/mempool_dpi.so: $(dpi)
	mkdir -p ${buildpath}/${dpi_library}
	$(CXX) -shared -m64 -o ${buildpath}/${dpi_library}/mempool_dpi.so $?

clean:
	rm -rf ${buildpath}

.PHONY: build lib sim simc clean
