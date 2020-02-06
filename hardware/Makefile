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

# build path
buildpath      ?= build
# questa library
library        ?= work
# dpi library
dpi_library    ?= work-dpi
# Top level module to compile
top_level      ?= mempool_tb
# QuestaSim Version
questa_version ?= -2019.3
# QuestaSim Commands
questa_cmd     ?=

ifndef QUESTASIM_HOME
	QUESTASIM_HOME = /usr/pack/questa-2019.3-kgf/questasim
# 	$(error QUESTASIM_HOME not set - please point your QUESTASIM_HOME variable to your QuestaSim installation)
endif

questa_cmd += -voptargs=+acc
ifdef preload
	questa_cmd += +PRELOAD=$(preload)
endif
questa_cmd += -sv_lib ${dpi_library}/mempool_dpi

# DPI source files
dpi   := $(patsubst tb/dpi/%.cpp,${buildpath}/${dpi_library}/%.o,$(wildcard tb/dpi/*.cpp))
trace := $(patsubst ${buildpath}/%.dasm,${buildpath}/%.log,$(wildcard ${buildpath}/*.dasm))

VLOG_ARGS += -suppress vlog-2583 -suppress vlog-13314 -suppress vlog-13233

build: bender lib ${buildpath}/${dpi_library}/mempool_dpi.so
	./bender script vsim --vlog-arg="$(VLOG_ARGS)" -t rtl -t asic -t mempool_test > ${buildpath}/compile.tcl
	echo "exit" >> ${buildpath}/compile.tcl
	cd ${buildpath} && questa${questa_version} vsim -c -do compile.tcl

lib:
	mkdir -p ${buildpath}
	mkdir -p ${buildpath}/${library}
	cd ${buildpath} && questa${questa_version} vlib work && chmod +w modelsim.ini && questa${questa_version} vmap work work

sim: build
	cd ${buildpath} && questa${questa_version} vsim $(questa_cmd) ${library}.${top_level}

simc: build
	cd ${buildpath} && questa${questa_version} vsim -c $(questa_cmd) ${library}.${top_level}

trace: $(trace)

${buildpath}/%.log: ${buildpath}/%.dasm
	mkdir -p ${buildpath}
	../riscv-isa-sim/build/spike-dasm < $< > $@

# Bender
bender: Makefile
	curl --proto '=https' --tlsv1.2 -sSf https://iis-people.ee.ethz.ch/~andkurt/bender-init \
		| sh -s -- 0.13.3
	touch bender

# DPIs
${buildpath}/${dpi_library}/%.o: tb/dpi/%.cpp
	mkdir -p ${buildpath}/${dpi_library}
	$(CXX) -shared -fPIC -std=c++11 -Bsymbolic -c $< -I${QUESTASIM_HOME}/include -o $@

${buildpath}/${dpi_library}/mempool_dpi.so: $(dpi)
	mkdir -p ${buildpath}/${dpi_library}
	$(CXX) -shared -m64 -o ${buildpath}/${dpi_library}/mempool_dpi.so $?

clean:
	rm -rf ${buildpath}

.PHONY: build lib sim simc clean bender
