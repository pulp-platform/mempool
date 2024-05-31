# Copyright 2021 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Author: Diyou Shen, ETH Zurich

# --------------
# environment
# --------------

SHELL = /usr/bin/env bash
ROOT_DIR := $(patsubst %/,%, $(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
MEMPOOL_DIR := $(shell git rev-parse --show-toplevel 2>/dev/null || echo $$MEMPOOL_DIR)

hw_path        	?= $(abspath $(MEMPOOL_DIR)/hardware)
app_path 				?= $(abspath $(MEMPOOL_DIR)/software/apps)
python          = python3
config 					?= mempool_spatz4_fpu
size 						?= 4096
cores						?= 64
iter 						?= 128
sim 						?= simcvcs
log 						?= true
outfile					?= false

# --------------
# build
# --------------

# Build bootrom and spatz
.PHONY: generate
generate:
	bender update
	config=$(config) make -C $(abspath $(MEMPOOL_DIR)) update_opcodes
	config=$(config) make -BC $(hw_path) src/bootrom.sv buildspatz

# Clean log and software configurations
.PHONY: log_clean
log_clean:
	make -C $(app_path) clean config=$(config)
	rm -vf *.log

# This target is run before switching configurations
# Clean hardware configurations
.PHONY: clean
clean:
	rm -vf *.json
	make -C $(hw_path) clean

# Clean results folder, use with causion
.PHONY: clean-all
clean-all: log_clean clean
	rm -vf results/*.txt

# --------------
# kernel
# --------------

# Normal dotp kernel
.PHONY: dotp
dotp: log_clean
	$(python) $(ROOT_DIR)/gen_config.py "dotp" 32 $(size) $(cores)
	$(python) $(app_path)/spatz_apps/sp-dotp/script/gen_data.py --cfg $(ROOT_DIR)/dotp.json
	config=$(config) make -C $(app_path) spatz_apps/sp-dotp >> $(ROOT_DIR)/buildsw.log
	if [ "$(log)" = "true" ]; then \
		config=$(config) make -C $(hw_path) $(sim) app=spatz_apps/sp-dotp >> $(ROOT_DIR)/result.log; \
		if [ "$(outfile)" = "false" ]; then \
			$(python) $(ROOT_DIR)/write_result.py $(ROOT_DIR)/result.log $(ROOT_DIR)/results/$(config)_dotp_$(cores).txt $(config); \
		else \
			$(python) $(ROOT_DIR)/write_result.py $(ROOT_DIR)/result.log $(ROOT_DIR)/results/$(outfile).txt $(config); \
		fi \
	else \
		config=$(config) make -C $(hw_path) $(sim) app=spatz_apps/sp-dotp; \
	fi

.PHONY: dotp-opt
dotp-opt: log_clean
	$(python) $(ROOT_DIR)/gen_config.py "dotp" 32 $(size) $(cores)
	$(python) $(app_path)/spatz_apps/sp-dotp-opt/script/gen_data.py --cfg $(ROOT_DIR)/dotp.json
	config=$(config) make -C $(app_path) spatz_apps/sp-dotp-opt >> $(ROOT_DIR)/buildsw.log
	if [ "$(log)" = "true" ]; then \
		config=$(config) make -C $(hw_path) $(sim) app=spatz_apps/sp-dotp-opt >> $(ROOT_DIR)/result.log; \
		if [ "$(outfile)" = "false" ]; then \
			$(python) $(ROOT_DIR)/write_result.py $(ROOT_DIR)/result.log $(ROOT_DIR)/results/$(config)_dotp_opt_$(cores).txt $(config); \
		else \
			$(python) $(ROOT_DIR)/write_result.py $(ROOT_DIR)/result.log $(ROOT_DIR)/results/$(outfile).txt $(config); \
		fi \
	else \
		config=$(config) make -C $(hw_path) $(sim) app=spatz_apps/sp-dotp-opt; \
	fi

# many-core version fft
.PHONY: fft
fft: log_clean
	$(python) $(ROOT_DIR)/gen_config.py "fft" 32 $(size) $(cores) 1 1 0
	$(python) $(app_path)/spatz_apps/sp-fft/script/gen_data.py --cfg $(ROOT_DIR)/fft.json
	config=$(config) make -C $(app_path) spatz_apps/sp-fft >> $(ROOT_DIR)/buildsw.log
	if [ "$(log)" = "true" ]; then \
		config=$(config) make -C $(hw_path) $(sim) app=spatz_apps/sp-fft >> $(ROOT_DIR)/result.log; \
		if [ "$(outfile)" = "false" ]; then \
			$(python) $(ROOT_DIR)/write_result.py $(ROOT_DIR)/result.log $(ROOT_DIR)/results/$(config)_fft_$(cores).txt $(config); \
		else \
			$(python) $(ROOT_DIR)/write_result.py $(ROOT_DIR)/result.log $(ROOT_DIR)/results/$(outfile).txt $(config); \
		fi \
	else \
		config=$(config) make -C $(hw_path) $(sim) app=spatz_apps/sp-fft; \
	fi

.PHONY: fft-multi
fft-multi: log_clean
	@case "$(config)" in \
	mempool*) \
		$(python) $(ROOT_DIR)/gen_config.py "fft-multi" 32 $(size) $(cores) 1 1 0 64;; \
	minpool*spatz4*) \
		$(python) $(ROOT_DIR)/gen_config.py "fft-multi" 32 $(size) $(cores) 1 1 0 4;; \
	minpool*spatz2*) \
		$(python) $(ROOT_DIR)/gen_config.py "fft-multi" 32 $(size) $(cores) 1 1 0 8;; \
	*) \
		$(python) $(ROOT_DIR)/gen_config.py "fft-multi" 32 $(size) $(cores) 1 1 0 128;; \
	esac
	$(python) $(app_path)/spatz_apps/sp-fft-multi/script/gen_data.py --cfg $(ROOT_DIR)/fft.json
	config=$(config) make -C $(app_path) spatz_apps/sp-fft-multi >> $(ROOT_DIR)/buildsw.log
	if [ "$(log)" = "true" ]; then \
		config=$(config) make -C $(hw_path) $(sim) app=spatz_apps/sp-fft-multi >> $(ROOT_DIR)/result.log; \
		if [ "$(outfile)" = "false" ]; then \
			$(python) $(ROOT_DIR)/write_result.py $(ROOT_DIR)/result.log $(ROOT_DIR)/results/$(config)_fft_$(cores).txt $(config); \
		else \
			$(python) $(ROOT_DIR)/write_result.py $(ROOT_DIR)/result.log $(ROOT_DIR)/results/$(outfile).txt $(config); \
		fi \
	else \
		config=$(config) make -C $(hw_path) $(sim) app=spatz_apps/sp-fft-multi; \
	fi

# bandwidth test
.PHONY: bandwidth
bandwidth: log_clean
	@case "$(config)" in \
	mempool*) \
		$(python) $(ROOT_DIR)/gen_config.py "bandwidth" 32 2048 $(cores) 16 $(iter) 0;; \
	minpool*) \
		$(python) $(ROOT_DIR)/gen_config.py "bandwidth" 32 128 $(cores) 16 $(iter) 0;; \
	*) \
		$(python) $(ROOT_DIR)/gen_config.py "bandwidth" 32 8192 $(cores) 32 $(iter) 0;; \
	esac
	$(python) $(app_path)/spatz_apps/bandwidth-test/script/gen_data.py --cfg $(ROOT_DIR)/bw.json
	config=$(config) make -C $(app_path) spatz_apps/bandwidth-test >> $(ROOT_DIR)/buildsw.log
	if [ "$(log)" = "true" ]; then \
		config=$(config) make -C $(hw_path) $(sim) app=spatz_apps/bandwidth-test >> $(ROOT_DIR)/result.log; \
		if [ "$(outfile)" = "false" ]; then \
			$(python) $(ROOT_DIR)/write_result.py $(ROOT_DIR)/result.log $(ROOT_DIR)/results/$(config)_dotp_$(cores).txt $(config); \
		else \
			$(python) $(ROOT_DIR)/write_result.py $(ROOT_DIR)/result.log $(ROOT_DIR)/results/$(outfile).txt $(config); \
		fi \
	else \
		config=$(config) make -C $(hw_path) $(sim) app=spatz_apps/bandwidth-test; \
	fi

# fmatmul kernel, only support square matrix when using this Makefile
.PHONY: fmatmul
fmatmul: log_clean
	$(python) $(ROOT_DIR)/gen_config.py "fmatmul" 32 $(size) $(cores)
	$(python) $(app_path)/spatz_apps/sp-fmatmul-opt/script/gen_data.py --cfg $(ROOT_DIR)/matmul.json
	config=$(config) make -C $(app_path) spatz_apps/sp-fmatmul-opt >> $(ROOT_DIR)/buildsw.log
	if [ "$(log)" = "true" ]; then \
		config=$(config) make -C $(hw_path) $(sim) app=spatz_apps/sp-fmatmul-opt >> $(ROOT_DIR)/result.log; \
		if [ "$(outfile)" = "false" ]; then \
			$(python) $(ROOT_DIR)/write_result.py $(ROOT_DIR)/result.log $(ROOT_DIR)/results/$(config)_fmatmul.txt $(config); \
		else \
			$(python) $(ROOT_DIR)/write_result.py $(ROOT_DIR)/result.log $(ROOT_DIR)/results/$(outfile).txt $(config); \
		fi \
	else \
		config=$(config) make -C $(hw_path) $(sim) app=spatz_apps/sp-fmatmul-opt; \
	fi

# --------------
# help
# --------------

help:
	@echo ""
	@echo "--------------------------------------------------------------------------------------------------------"
	@echo "Spatz Benchmark Makefile"
	@echo "--------------------------------------------------------------------------------------------------------"
	@echo "targets:"
	@echo ""
	@echo "dotp:         run the *sp-dotp* kernel, needs input of size and number of cores"
	@echo "dotp-opt:     run the *sp-dotp-opt* kernel, needs input of size and number of cores"
	@echo "fft:          run the *sp-fft* kernel, needs input of size and number of cores"
	@echo "fft-multi:    run the *sp-fft* kernel, needs input of size and number of cores working on one fft"
	@echo "              all cores will be used to run multiple fft in parallel."
	@echo "              only support minpool-spatz4*, mempool-spatz4* and terapool-spatz8 currently."
	@echo "bandwidth:    run the *bandwidth test*, size and step will be calculated based on config,"
	@echo "              only need the input of cores and number of iteration"
	@echo "fmatmul:      run the *sp-fmatmul-opt* kernel. only support nxnxn kernel now"
	@echo ""
	@echo "clean-all:    cleans all generated files, including results"
	@echo "clean:        cleans configuration. call this target after changing the configurations"
	@echo "generate:     generate bootrom and spatz package, call it after changing the configurations."
	@echo ""
	@echo "--------------------------------------------------------------------------------------------------------"
	@echo "inputs | default            | descriptions"
	@echo ""
	@echo "config | mempool_spatz4_fpu | hardware configurations"
	@echo "size   | 4096               | size of the kernel"
	@echo "cores  | 64                 | number of cores used in calculation"
	@echo "iter   | 128                | iteration of tests, only valid for bandwidth test"
	@echo "sim    | simcvcs            | simulation tool: sim, simc, simcvcs"
	@echo "log    | true               | log data into result log?"
	@echo "outfile| false              | output file name, set false will not write into the file"
	@echo ""
	@echo "--------------------------------------------------------------------------------------------------------"
	@echo "Example of use:"
	@echo "make dotp config=mempool_spatz4_fpu size=16384 cores=64 log=false"
	@echo "make fft config=mempool_spatz4_fpu size=512 cores=8 log=true outfile=mempool_spatz4_fft"
	@echo "make clean generate fft-multi config=terapool_spatz8_fpu size=2048 cores=32 log=false"
	@echo "make bandwidth config=minpool_spatz4_fpu cores=4 iter=256 log=false"
	@echo ""
