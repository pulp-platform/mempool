# Copyright 2024 ETH Zurich and University of Bologna.
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51

# Samuel Riedel <sriedel@iis.ee.ethz.ch>

SHELL = /usr/bin/env bash
ROOT_DIR := $(patsubst %/,%, $(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
RUNTIME_DIR := $(abspath $(ROOT_DIR)/../../../software/runtime)

regtool ?= $(abspath $(ROOT_DIR)/../../deps/register_interface/vendor/lowrisc_opentitan/util/regtool.py)

RTL := $(patsubst $(ROOT_DIR)/%.hjson,%,$(shell find $(ROOT_DIR) -name "*.hjson"))

all: $(RTL)_reg_top.sv $(RUNTIME_DIR)/$(RTL).h

$(RTL)_reg_top.sv: %_reg_top.sv: %.hjson
	$(regtool) $^ -r -t $(ROOT_DIR)

$(RUNTIME_DIR)/$(RTL).h: $(RUNTIME_DIR)/%.h: %.hjson
	$(regtool) $^ -D -o $@

$(RTL).html: %.html: %.hjson
	$(regtool) $^ -d -o $@

clean:
	@rm -fv $(RTL)_reg_pkg.sv
	@rm -fv $(RTL)_reg_top.sv
	@rm -fv $(RTL).html
	@rm -fv $(RUNTIME_DIR)/$(RTL).h

.EXTRA_PREREQS:= $(abspath $(lastword $(MAKEFILE_LIST)))
