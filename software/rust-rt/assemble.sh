#!/bin/bash

# Copyright 2022 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -euxo pipefail

crate=rust-rt

# remove existing blobs because otherwise this will append object files to the old blobs
rm -f bin/*.a

exts=('i' 'ic' 'im' 'ima' 'imc' 'if' 'ifc' 'imf' 'imfc' 'ifd' 'ifdc' 'imfd' 'imfdc')

for ext in ${exts[@]}
do
    case $ext in

        *'d'*)
            abi='d'
            ;;
        
        *'f'*)
            abi='f'
            ;;
        
        *)
            abi=''
            ;;
    esac

    riscv64-unknown-elf-gcc -ggdb3 -fdebug-prefix-map=$(pwd)=/riscv-rt -c -mabi=ilp32${abi} -march=rv32${ext}_zicsr rrt0.S -o bin/$crate.o
    riscv64-unknown-elf-ar crs bin/riscv32${ext}-unknown-none-elf.a bin/$crate.o

    riscv64-unknown-elf-gcc -ggdb3 -fdebug-prefix-map=$(pwd)=/riscv-rt -c -mabi=lp64${abi} -march=rv64${ext}_zicsr rrt0.S -o bin/$crate.o
    riscv64-unknown-elf-ar crs bin/riscv64${ext}-unknown-none-elf.a bin/$crate.o
done

rm bin/$crate.o
