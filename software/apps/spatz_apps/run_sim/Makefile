# Copyright 2021 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Author: Diyou Shen, ETH Zurich

SHELL = /usr/bin/env bash
ROOT_DIR := $(patsubst %/,%, $(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
MEMPOOL_DIR := $(shell git rev-parse --show-toplevel 2>/dev/null || echo $$MEMPOOL_DIR)

hw_path        	?= $(abspath $(MEMPOOL_DIR)/hardware)
app_path 				?= $(abspath $(MEMPOOL_DIR)/software/apps)
python          ?= python3
config 					?= mempool_spatz4_fpu
size 						?= 4096
cores						?= 64
sim 						?= simcvcs
log 						?= true

.PHONY: json_clean
json_clean:
	rm -vf *.json

.PHONY: log_clean
log_clean:
	rm -vf *.log

.PHONY: txt_clean
txt_clean:
	rm -vf results/*.txt

.PHONY: clean
clean: json_clean
	make -C $(hw_path) clean

.PHONY: clean-all
clean-all: log_clean txt_clean clean

.PHONY: dotp
dotp: log_clean
	$(python) $(ROOT_DIR)/gen_config.py "dotp" 32 $(size) $(cores)
	$(python) $(app_path)/spatz_apps/sp-dotp/script/gen_data.py --cfg $(ROOT_DIR)/dotp.json
	config=$(config) make -C $(app_path) spatz_apps/sp-dotp
	config=$(config) make -C $(hw_path) $(sim) app=spatz_apps/sp-dotp >> $(ROOT_DIR)/result.log
	if [ "$(log)" = "true" ]; then \
		$(python) $(ROOT_DIR)/write_result.py $(ROOT_DIR)/result.log $(ROOT_DIR)/results/$(config)_dotp_$(cores).txt; \
	fi

.PHONY: dotp-opt
dotp-opt: log_clean
	$(python) $(ROOT_DIR)/gen_config.py "dotp" 32 $(size) $(cores)
	$(python) $(app_path)/spatz_apps/sp-dotp-opt/script/gen_data.py --cfg $(ROOT_DIR)/dotp.json
	config=$(config) make -C $(app_path) spatz_apps/sp-dotp-opt
	config=$(config) make -C $(hw_path) $(sim) app=spatz_apps/sp-dotp-opt >> $(ROOT_DIR)/result.log
	if [ "$(log)" = "true" ]; then \
		$(python) $(ROOT_DIR)/write_result.py $(ROOT_DIR)/result.log $(ROOT_DIR)/results/$(config)_dotp_opt_$(cores).txt; \
	fi

.PHONY: fft
fft: log_clean
	$(python) $(ROOT_DIR)/gen_config.py "fft" 32 $(size) $(cores)
	$(python) $(app_path)/spatz_apps/sp-fft/script/gen_data.py --cfg $(ROOT_DIR)/fft.json
	config=$(config) make -C $(app_path) spatz_apps/sp-fft
	config=$(config) make -C $(hw_path) $(sim) app=spatz_apps/sp-fft >> $(ROOT_DIR)/result.log
	if [ "$(log)" = "true" ]; then \
		$(python) $(ROOT_DIR)/write_result.py $(ROOT_DIR)/result.log $(ROOT_DIR)/results/$(config)_fft_$(cores).txt; \
	fi

# currently only run 256x256x256
.PHONY: fmatmul
fmatmul: log_clean
	$(python) $(ROOT_DIR)/gen_config.py "fmatmul" 256 256 256 32
	$(python) $(app_path)/spatz_apps/sp-fft/script/gen_data.py --cfg $(ROOT_DIR)/fft.json
	config=$(config) make -C $(app_path) spatz_apps/sp-fmatmul-opt
	config=$(config) make -C $(hw_path) $(sim) app=spatz_apps/sp-fmatmul-opt>> $(ROOT_DIR)/result.log
	if [ "$(log)" = "true" ]; then \
		$(python) $(ROOT_DIR)/write_result.py $(ROOT_DIR)/result.log $(ROOT_DIR)/results/$(config)_fmatmul.txt; \
	fi

# --------------
# help
# --------------

help:
	@echo ""
	@echo "Spatz Benchmark Makefile"
	@echo "-------------"
	@echo "targets:"
	@echo ""
	@echo "dotp:         run the sp-dotp kernel, needs input of size and number of cores"
	@echo "dotp-opt:     run the sp-dotp-opt kernel, needs input of size and number of cores"
	@echo "fft:          run the sp-fft kernel, needs input of size and number of cores"
	@echo "fmatmul:      run the sp-fmatmul-opt kernel. Currently will only run 256x256x256 kernel"
	@echo ""
	@echo "clean-all:    cleans all generated files, including results"
	@echo "clean:        cleans configuration. call before changing the configurations"
	@echo ""
	@echo "-------------"
	@echo "inputs | default 					 | descriptions"
	@echo ""
	@echo "config | mempool_spatz4_fpu | configurations"
	@echo "size   | 4096 							 | size of the kernel"
	@echo "cores  | 64 								 | number of cores used in calculation"
	@echo "sim    | simcvcs 					 | simulation tool"
	@echo "log    | true               | log data into results?"
	@echo ""
	@echo "Example of use: make -C PATH_TO_MF dotp config=mempool_spatz4_fpu size=16384 cores=64"
	@echo ""
