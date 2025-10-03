# Copyright 2025 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Danilo Cammarata <dcammarata@iis.ee.ethz.ch>
#

export BENDER_DIR=$(pwd)/hw/bender
echo "Exporting bender path to $BENDER_DIR"
export PATH=$BENDER_DIR:$PATH
unset BENDER_DIR
echo "Exporting SDK and GCC Toolchain paths"
export PATH=/usr/pack/riscv-1.0-kgf/riscv64-gcc-12.2.0/bin:$PATH
export PULP_RISCV_GCC_TOOLCHAIN=/usr/pack/riscv-1.0-kgf/riscv64-gcc-12.2.0
export PATH=/usr/pack/gcc-5.2.0-af/x86_64-rhe6-linux/bin:$PATH
export CXX=g++-13.2.0
export Questa=questa-2023.4
export Verilator="verilator-5.020 verilator"
export VerilatorRoot=/usr/pack/verilator-5.006-zr/verilator-5.006
export Gcc=
export XTEN=im_ziscr
export XLEN=64
