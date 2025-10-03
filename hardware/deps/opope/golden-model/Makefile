# Copyright 2025 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Danilo Cammarata <dcammarata@iis.ee.ethz.ch>
#
# O-POPE Golden Model Makefile

SHELL   := /bin/bash
CUR_DIR := $(shell pwd)
PENV    := $(CUR_DIR)/venv
SW      ?= 

## Perform Matrix-Matrix Operations of the kins _Z = Y (op2) (X (op1) W)_
## We assume X is _MxN_, W is _NxK_, while Y and Z are _MxK_

# Tensors Dimensions
M ?= 3
N ?= 3
K ?= 3
transpose ?= 1

# FP format
fp_fmt ?= FP16

check_sw:
	mkdir -p $(SW)

check_penv: check_sw
ifndef PENV
	$(error PENV is undefined. Make sure to export       \
	PENV=<absolute_path_your_pythonenv> before continue.)
	python3 -m venv $(PENV)
	source .venv/bin/activate
	pip3 install numpy
	pip3 install torch
endif

# The current Makefile can be used as follows:
# make $(operation)      -> execute any of the supported GEMM-Ops operation (Z = (X op1 W) op2 Y)
# Set the tensor dimensions while launching the Makefile. For example, in order to run a GEMM
# between three 64x64 matrices, run:
# `make clean gemm M=64 N=64 K=64`

addmax: check_penv
	mkdir -p $@/txt;                          \
	cd $(PENV);                               \
	source ./bin/activate;                    \
	cd $(CUR_DIR)/$(fp_fmt);                  \
	python3 ./scripts/$@.py                   \
	--m_size $(M) --n_size $(N) --k_size $(K) \
	--inc_dir $(SW)                           \
	--txt_dir $(CUR_DIR)/$@/txt;              \
	cd $(PENV);                               \
	deactivate

addmin: check_penv
	mkdir -p $@/txt;                          \
	cd $(PENV);                               \
	source ./bin/activate;                    \
	cd $(CUR_DIR)/$(fp_fmt);                  \
	python3 ./scripts/$@.py                   \
	--m_size $(M) --n_size $(N) --k_size $(K) \
	--inc_dir $(SW)                           \
	--txt_dir $(CUR_DIR)/$@/txt;              \
	cd $(PENV);                               \
	deactivate

gemm: check_penv
	mkdir -p $@/txt;                          							\
	cd $(PENV);                               							\
	source ./bin/activate;                    							\
	cd $(CUR_DIR)/$(fp_fmt);                  							\
	python3 ./scripts/$@.py                   							\
	--m_size $(M) --n_size $(N) --k_size $(K) 							\
	--inc_dir $(SW)                           							\
	--txt_dir $(CUR_DIR)/$@/txt --transpose $(transpose);  \
	cd $(PENV);                               							\
	deactivate

matmul: check_penv
	mkdir -p $@/txt;                          \
	cd $(PENV);                               \
	source ./bin/activate;                    \
	cd $(CUR_DIR)/$(fp_fmt);                  \
	python3 ./scripts/$@.py                   \
	--m_size $(M) --n_size $(N) --k_size $(K) \
	--inc_dir $(SW)                           \
	--txt_dir $(CUR_DIR)/$@/txt;              \
	cd $(PENV);                               \
	deactivate

maxmin: check_penv
	mkdir -p $@/txt;                          \
	cd $(PENV);                               \
	source ./bin/activate;                    \
	cd $(CUR_DIR)/$(fp_fmt);                  \
	python3 ./scripts/$@.py                   \
	--m_size $(M) --n_size $(N) --k_size $(K) \
	--inc_dir $(SW)/inc                       \
	--txt_dir $(CUR_DIR)/$@/txt;              \
	cd $(PENV);                               \
	deactivate

minmax: check_penv
	mkdir -p $@/txt;                          \
	cd $(PENV);                               \
	source ./bin/activate;                    \
	cd $(CUR_DIR)/$(fp_fmt);                  \
	python3 ./scripts/$@.py                   \
	--m_size $(M) --n_size $(N) --k_size $(K) \
	--inc_dir $(SW)                           \
	--txt_dir $(CUR_DIR)/$@/txt;              \
	cd $(PENV);                               \
	deactivate

mulmax: check_penv
	mkdir -p $@/txt;                          \
	cd $(PENV);                               \
	source ./bin/activate;                    \
	cd $(CUR_DIR)/$(fp_fmt);                  \
	python3 ./scripts/$@.py                   \
	--m_size $(M) --n_size $(N) --k_size $(K) \
	--inc_dir $(SW)                           \
	--txt_dir $(CUR_DIR)/$@/txt;              \
	cd $(PENV);                               \
	deactivate

mulmin: check_penv
	mkdir -p $@/txt;                          \
	cd $(PENV);                               \
	source ./bin/activate;                    \
	cd $(CUR_DIR)/$(fp_fmt);                  \
	python3 ./scripts/$@.py                   \
	--m_size $(M) --n_size $(N) --k_size $(K) \
	--inc_dir $(SW)                           \
	--txt_dir $(CUR_DIR)/$@/txt;              \
	cd $(PENV);                               \
	deactivate

golden-clean:
	rm -rf FP16/net_parameters.h
	rm -rf FP8/net_parameters.h
	rm -rf FP16/scripts/__pycache__
	rm -rf FP8/scripts/__pycache__
	rm -rf addmax addmin gemm maxmin minmax mulmax mulmin
