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

# Author: Samuel Riedel, ETH Zurich

PULP_APP = gradient
PULP_APP_CL_SRCS =
PULP_APP_FC_SRCS = main.c
gradient_OBJS += lib/gradient_riscv.o
PULP_CFLAGS = -O3 -g -I lib

CC ?= gcc
CXX ?= g++
LLVM_CONFIG ?= llvm-config

# Halide Path
HALIDE_INSTALL_DIR ?=
HALIDE_INCLUDE = ${HALIDE_INSTALL_DIR}/include
HALIDE_LIB = ${HALIDE_INSTALL_DIR}/bin

# Source files
PIPELINE = gradient

.PHONY: ${PIPELINE}

${PIPELINE}:
	cd lib; \
	${CXX} ${PIPELINE}.cpp -g -I ${HALIDE_INCLUDE} -L ${HALIDE_LIB} -lHalide -lpthread -ldl -std=c++11 -o ${PIPELINE}; \
	LD_LIBRARY_PATH=${HALIDE_LIB} ./${PIPELINE}

include $(PULP_SDK_HOME)/install/rules/pulp_rt.mk
