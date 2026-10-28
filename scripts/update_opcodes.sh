#!/bin/bash
# Copyright 2020 ETH Zurich and University of Bologna.
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51

# Generate the opcodes for the Snitch system.
set -e
ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)

OPCODES=($(cat "$(dirname "${BASH_SOURCE[0]}")/opcodes.txt"))

INSTR_SV=$ROOT/hardware/deps/snitch/src/riscv_instr.sv

cat > $INSTR_SV <<- EOM
// Copyright 2023 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

EOM
echo -e "// verilog_lint: waive-start parameter-name-style" >> $INSTR_SV
riscv_opcodes -sverilog --warn-overlap ${OPCODES[@]}
# Dump riscv_opcodes output to the instruction file
cat inst.sverilog >> $INSTR_SV
# Delete riscv_opcodes artifacts
rm inst.sverilog instr_dict.json
echo -e "// verilog_lint: waive-stop parameter-name-style" >> $INSTR_SV


ENCODING_H=$ROOT/software/runtime/encoding.h

cat > $ENCODING_H <<- EOM
// Copyright 2023 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

#define DEFAULT_RSTVEC     0x00001000
#define CLINT_BASE         0x02000000
#define CLINT_SIZE         0x000c0000
#define EXT_IO_BASE        0x40000000
#define DRAM_BASE          0x80000000

EOM
riscv_opcodes -c --warn-overlap ${OPCODES[@]}
# Dump riscv_opcodes output to the instruction file
cat encoding.out.h >> $ENCODING_H
# Delete riscv_opcodes artifacts
rm encoding.out.h instr_dict.json
