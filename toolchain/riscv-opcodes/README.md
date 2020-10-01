riscv-opcodes
===========================================================================

This repo enumerates standard RISC-V instruction opcodes and control and
status registers, as well as some custom modifications.  It also contains a
script to convert them into several formats (C, SystemVerilog, Scala, LaTeX),
starting from their high-level, human-readable description.

## Practical info
- Every output of the parser is generated inside this folder; tools which
  need such automatically generated files must use soft link to point to them.
  For example, supposing `RISCV_ISA_SIM_TOOL` is set to the source code directory of
  the Spike simulator:

  ```bash
  ln -sfr encoding_out.h $RISCV_ISA_SIM_TOOL/encoding.h
  ```

  Example of where the outputs of `parse-opcodes` are used in other projects

  | Parser output  | Destination                                    |
  |:--------------:|:-----------------------------------------------|
  | encoding_out.h | riscv-gnu-toolchain/riscv-binutils-gdb/include/opcode/riscv-opc.h <br> riscv-isa-sim/riscv/encoding.h <br> riscv-pk/machine/encoding.h <br> riscv-tests/env/encoding.h <br> riscv-openocd/src/target/riscv/encoding.h <br> _custom use_ i.e. apps/common/encoding.h |
  | inst.sverilog  | snitch/src/riscv_instr.sv |

- opcodes description files organization matches the same of the official
  repository upstream [riscv-opcodes](https://github.com/riscv/riscv-opcodes),
  with the addition of several custom instruction set extensions: you can
  add your own custom extensions as text file in the root, subsequently
  adding it to the variable `MY_OPCODES` of the `Makefile`
- in the `Makefile`, you can select which opcodes files not to take into account
  for the parsing script execution, basing on the target architecture, by
  listing them in the variable `DISCARDED_OPCODES`;
- opcodes files from the official 128-bit extension have not been introduced
  due to the other changes which they imply to other opcodes specifications.

## Known problems
1. Some instructions of the still unofficial bit manipulation extension
  (`opcodes-rv32b` and `opcodes-rv64b`, discarded by default in the parsing)
  overlap with some of the Xpulp extension (`opcodes-xpulpimg`, subset of Xpulp).
