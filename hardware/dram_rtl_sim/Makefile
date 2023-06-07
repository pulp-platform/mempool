BENDER ?= bender
VLOG_ARGS = -svinputport=compat -override_timescale 1ns/1ps -suppress 2583 -suppress 13314
library ?= work
top_level ?= axi_to_dram_tb
app ?= ../../DRAMSys/hello_world


# Path to DRAMsyslib
dramsys_resouces_path ?= ../dramsys_lib/resources/
dramsys_simconfig_path ?= ../dramsys_lib/resources/simulations/hbm2-example.json
dramsys_lib_path ?= ../dramsys_lib
# QuestaSim arguments
questa_args    ?=
questa_args += +DRAMSYS_RES=$(dramsys_resouces_path) +DRAMSYS_CONF=$(dramsys_simconfig_path)
questa_args += -sv_lib $(dramsys_lib_path)/libDRAMSysLibrary
questa_args += +app=$(app) 

all: compile
	cd vsim && questa vsim $(library).$(top_level) -t 1ps -voptargs=+acc $(questa_args) -do start.tcl

compile: vsim/compile.tcl
	echo "exit" >> vsim/compile.tcl
	cd vsim && questa vsim -c -do compile.tcl

vsim/compile.tcl: Bender.yml Makefile $(shell find src -type f) $(shell find test -type f) 
	$(BENDER) script vsim -t test -t rtl --vlog-arg="$(VLOG_ARGS)" > $@

clean:
	cd vsim && rm -rf work/ vsim.wlf  transcript  modelsim.ini compile.tcl
