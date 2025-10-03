# Copyright 2025 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Andrea Belano <andrea.belano@studio.unibo.it>
# Danilo Cammarata <dcammarata@iis.ee.ethz.ch>
#

#!/bin/bash
Red="\e[31m"
Green="\e[32m"
EndColor="\e[0m"

if [ -z "$Target" ]; then
    echo -e "${Red}Error: no Target defined. Set the  Target variable to "vsim" or "verilator" before continue.${EndColor}"
else

  BASE_TIMEOUT=500

  PARAMS=(
      96 96 96
      128 128 128
      12 16 16
      24 16 16
      48 32 32
      30 32 17
      24 32 1
      31 32 16
      17 32 16
      31 32 31
      17 32 3
      5  32 17
      5  32 3
      36 31 32
      12 31 16
      23 31 31
      24 17 32
      24 20 32
      23 17 33
      23 20 33
      3  11 32
      17 13 16
      17 13 17
  )

  i=0
  error=0

  while [[ $i -lt ${#PARAMS[@]} ]]
  do
      M=${PARAMS[$i]}
      N=${PARAMS[$(( $i + 1 ))]}
      K=${PARAMS[$(( $i + 2 ))]}

      i=$(( $i + 3 ))

      make hw-clean hw-build target=$Target 1>/dev/null 2>&1
      make golden M=$M N=$N K=$K 1>/dev/null 2>&1
      make sw-clean sw-build 1>/dev/null 2>&1
      timeout $BASE_TIMEOUT make hw-run target=$Target > $PWD/target/sim/$Target/transcript_${M}_${N}_${K}
      if grep -rn "\[TB\] - Success!" "$PWD/target/sim/$Target/transcript_${M}_${N}_${K}" 1>/dev/null 2>&1; then
          echo -e "${Green}OK  ${EndColor}: M=$M N=$N K=$K"
      else
          echo -e "${Red}ERROR ${EndColor}: M=$M N=$N K=$K"
          ((error++))
      fi
  done

  if [ "$error" -gt 0 ]; then
    exit 1
  fi

fi
