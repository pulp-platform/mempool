#!/usr/bin/env bash

# Copyright 2021 ETH Zurich and University of Bologna.
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51

# Author: Sergio Mazzola, ETH Zurich

# Automatize systolic experiments benchmarking

if [ $(basename "$PWD") != "hardware" ]; then
  echo "ERROR: run this script from the hardware directory"
  exit 1
fi

run_systolic() {
  # mandatory inputs
  if [ -z "$1" ]; then
    echo "ERROR: APP not defined"
    exit 1
  fi
  local APP=$1
  if [ -z "$2" ]; then
    echo "ERROR: DIM_M not defined"
    exit 1
  fi
  local DIM_M=$2
  if [ -z "$3" ]; then
    echo "ERROR: DIM_N not defined"
    exit 1
  fi
  local DIM_N=$3
  # optional inputs
  if [ -z "$4" ]; then
    local DIM_P=""
  else
    local DIM_P=$4
  fi
  if [ -z "$5" ]; then
    local TAG=""
  else
    local TAG="_$5"
  fi
  if [ -z "$6" ]; then
    local REPS=""
  else
    local REPS=$6
  fi
  if [ -z "$7" ]; then
    local SYS_LEN=""
  else
    local SYS_LEN=$7
  fi


  make clean
  mkdir -p ./build

  # compile software
  DIM_M=$DIM_M DIM_N=$DIM_N DIM_P=$DIM_P \
  REP_COUNT=$REPS SYSTOLIC_LENGTH=$SYS_LEN \
    make -C ../software/apps systolic/${APP} 2>&1 | tee ./build/gcc.log
  # execute simcvcs and parse return status
  app=systolic/${APP} make simcvcs 2>&1 | tee ./build/simcvcs.log
  local RET=$(grep '\[EOC\]' ./build/simcvcs.log | grep -Poh -- '(?<=\(retval = )-?[0-9]+(?=\))')
  echo "Parsed return status: $RET"
  if [ $RET -ne 0 ]; then
    exit $RET
  fi

  # parse traces
  make trace || exit 1
  make tracemac || exit 1
  #app=systolic/${APP} make tracevis || exit 1

  # save results
  cd results
  local DIR=`ls -td -- */ | head -n 1`
  mkdir -p ./$DIR/traces
  mv ./$DIR/*.trace ./$DIR/traces

  mkdir -p ./$DIR/logs
  mv ../build/gcc.log ./$DIR/logs
  mv ../build/simcvcs.log ./$DIR/logs
  git diff > ./$DIR/logs/git_diff.log

  mkdir -p ./$DIR/app
  cp ../../software/bin/systolic/${APP} ../../software/bin/systolic/${APP}.dump ./$DIR/app

  mv ../build/tracemac* ./$DIR/
  #mv ../build/tracevis* ./$DIR/

  local TIMESTAMP=`date +"%Y%m%d_%H%M%S_$(git rev-parse --short HEAD)"`
  # if DIM_P is empty
  if [ -z "$DIM_P" ]; then
    local NAME=${APP}_${DIM_M}_${DIM_N}${TAG}__${TIMESTAMP}
  else
    local NAME=${APP}_${DIM_M}_${DIM_N}_${DIM_P}${TAG}__${TIMESTAMP}
  fi
  mv $DIR ${NAME}
  cd ..
  rm -rf ../software/bin/systolic/${APP} ../software/bin/systolic/${APP}.dump
}

export MEMPOOL_CONFIGURATION=systolic

# run_systolic matmul_qlr_3x3 squaresquare 144 370 144
# run_systolic matmul_qlr_3x4 squaresquare 144 370 128
# run_systolic matmul_qlr_4x2_hybrid squaresquare 192 370 96
# run_systolic matmul_qlr_4x4_hybrid squaresquare 192 320 128
# run_systolic matmul_qlr_4x4_hybrid_preload squaresquare 192 330 120
# run_systolic matmul_qlr_4x4_hybrid_preload_row squaresquare 192 330 120
# run_systolic matmul_qlr_4x4_hybrid_preload_row_wide rowwise 96 300 248

# run_systolic conv_qlr 255 243 "" "reps_1_len_256" 1 256
# run_systolic conv_qlr 254 243 "" "reps_1_len_128" 1 128
# run_systolic conv_qlr 252 246 "" "reps_1_len_64"  1 64
# run_systolic conv_qlr 248 249 "" "reps_1_len_32"  1 32
# run_systolic conv_qlr 240 258 "" "reps_1_len_16"  1 16
# run_systolic conv_qlr 510 120 "" "reps_1_len_256" 1 256
# run_systolic conv_qlr 508 120 "" "reps_1_len_128" 1 128
# run_systolic conv_qlr 504 123 "" "reps_1_len_64"  1 64
# run_systolic conv_qlr 496 123 "" "reps_1_len_32"  1 32
# run_systolic conv_qlr 480 129 "" "reps_1_len_16"  1 16
# run_systolic conv_qlr 765  81 "" "reps_1_len_256"  1 256
# run_systolic conv_qlr 762  81 "" "reps_1_len_128"  1 128
# run_systolic conv_qlr 756  81 "" "reps_1_len_64"   1 64
# run_systolic conv_qlr 744  81 "" "reps_1_len_32"   1 32
# run_systolic conv_qlr 720  84 "" "reps_1_len_16"   1 16

# run_systolic conv_qlr_2  510 120 "" "reps_1_len_256" 1 256
# run_systolic conv_qlr_2  508 120 "" "reps_1_len_128" 1 128
# run_systolic conv_qlr_2  504 123 "" "reps_1_len_64"  1 64
# run_systolic conv_qlr_2  496 123 "" "reps_1_len_32"  1 32
# run_systolic conv_qlr_2  480 129 "" "reps_1_len_16"  1 16
# run_systolic conv_qlr_2 1020  60 "" "reps_1_len_256" 1 256
# run_systolic conv_qlr_2 1016  60 "" "reps_1_len_128" 1 128
# run_systolic conv_qlr_2 1008  60 "" "reps_1_len_64"  1 64
# run_systolic conv_qlr_2  992  60 "" "reps_1_len_32"  1 32
# run_systolic conv_qlr_2  960  63 "" "reps_1_len_16"  1 16
# run_systolic conv_qlr_2 1530  30 "" "reps_1_len_256" 1 256
# run_systolic conv_qlr_2 1524  39 "" "reps_1_len_128" 1 128
# run_systolic conv_qlr_2 1512  39 "" "reps_1_len_64"  1 64
# run_systolic conv_qlr_2 1488  39 "" "reps_1_len_32"  1 32
# run_systolic conv_qlr_2 1440  42 "" "reps_1_len_16"  1 16

# # dir 1
# run_systolic conv_qlr 255 243 "" "reps_2_len_256" 2 256
# run_systolic conv_qlr 254 243 "" "reps_2_len_128" 2 128
# run_systolic conv_qlr 252 246 "" "reps_2_len_64"  2 64
# run_systolic conv_qlr 248 249 "" "reps_2_len_32"  2 32
# run_systolic conv_qlr 240 258 "" "reps_2_len_16"  2 16
# # dir 2
# run_systolic conv_qlr 510 120 "" "reps_2_len_256" 2 256
# run_systolic conv_qlr 508 120 "" "reps_2_len_128" 2 128
# run_systolic conv_qlr 504 123 "" "reps_2_len_64"  2 64
# run_systolic conv_qlr 496 123 "" "reps_2_len_32"  2 32
# run_systolic conv_qlr 480 129 "" "reps_2_len_16"  2 16
# # dir 3
# run_systolic conv_qlr 765  81 "" "reps_2_len_256" 2 256
# run_systolic conv_qlr 762  81 "" "reps_2_len_128" 2 128
# run_systolic conv_qlr 756  81 "" "reps_2_len_64"  2 64
# run_systolic conv_qlr 744  81 "" "reps_2_len_32"  2 32
# run_systolic conv_qlr 720  84 "" "reps_2_len_16"  2 16

# # dir 4
# run_systolic conv_qlr_2  510 120 "" "reps_2_len_256" 2 256
# run_systolic conv_qlr_2  508 120 "" "reps_2_len_128" 2 128
# run_systolic conv_qlr_2  504 123 "" "reps_2_len_64"  2 64
# run_systolic conv_qlr_2  496 123 "" "reps_2_len_32"  2 32
# run_systolic conv_qlr_2  480 129 "" "reps_2_len_16"  2 16
# # dir 5
# run_systolic conv_qlr_2 1020  60 "" "reps_2_len_256" 2 256
# run_systolic conv_qlr_2 1016  60 "" "reps_2_len_128" 2 128
# run_systolic conv_qlr_2 1008  60 "" "reps_2_len_64"  2 64
# run_systolic conv_qlr_2  992  60 "" "reps_2_len_32"  2 32
# run_systolic conv_qlr_2  960  63 "" "reps_2_len_16"  2 16
# # dir 6
# run_systolic conv_qlr_2 1530  30 "" "reps_2_len_256" 2 256
# run_systolic conv_qlr_2 1524  39 "" "reps_2_len_128" 2 128
# run_systolic conv_qlr_2 1512  39 "" "reps_2_len_64"  2 64
# run_systolic conv_qlr_2 1488  39 "" "reps_2_len_32"  2 32
# run_systolic conv_qlr_2 1440  42 "" "reps_2_len_16"  2 16

# # dir 7
# run_systolic conv_qlr_3 765 81 "" "reps_1_len_256" 1 256
# run_systolic conv_qlr_3 762 81 "" "reps_1_len_128" 1 128
# run_systolic conv_qlr_3 756 81 "" "reps_1_len_64"  1 64
# run_systolic conv_qlr_3 744 81 "" "reps_1_len_32"  1 32
# run_systolic conv_qlr_3 720 84 "" "reps_1_len_16"  1 16

# # dir 8
# run_systolic conv_qlr_3 765 81 "" "reps_2_len_256" 2 256
# run_systolic conv_qlr_3 762 81 "" "reps_2_len_128" 2 128
# run_systolic conv_qlr_3 756 81 "" "reps_2_len_64"  2 64
# run_systolic conv_qlr_3 744 81 "" "reps_2_len_32"  2 32
# run_systolic conv_qlr_3 720 84 "" "reps_2_len_16"  2 16

# # dir 1
run_systolic matmul_qlr_3x3                         48    1260  48  "square-square_16x16_16x16" "" "" # error!!!!!!
run_systolic matmul_qlr_3x3                         336   16    336 "square-square_16x16_16x16" "" ""
run_systolic matmul_qlr_3x3                         144   360   144 "square-square_16x16_16x16" "" ""
run_systolic matmul_qlr_3x3                         192   225   192 "square-square_16x16_16x16" "" ""
# dir 2
run_systolic matmul_qlr_3x4                         48    1070  64  "square-square_16x16_16x16" "" "" # error!!!!!!
run_systolic matmul_qlr_3x4                         288   19    384 "square-square_16x16_16x16" "" ""
run_systolic matmul_qlr_3x4                         144   285   192 "square-square_16x16_16x16" "" ""
run_systolic matmul_qlr_3x4                         192   165   256 "square-square_16x16_16x16" "" ""
# dir 3
run_systolic matmul_qlr_3x6                         48    825   96  "square-square_16x16_16x16" "" "" # error!!!!!!
run_systolic matmul_qlr_3x6                         240   12    480 "square-square_16x16_16x16" "" ""
run_systolic matmul_qlr_3x6                         96    360   192 "square-square_16x16_16x16" "" ""
run_systolic matmul_qlr_3x6                         144   190   288 "square-square_16x16_16x16" "" ""
# dir 4
run_systolic matmul_qlr_4x2_hybrid                  64    1265  32  "square-square_16x16_16x16" "" "" # error!!!!!!
run_systolic matmul_qlr_4x2_hybrid                  448   13    256 "square-square_16x16_16x16" "" ""
run_systolic matmul_qlr_4x2_hybrid                  192   310   128 "square-square_16x16_16x16" "" ""
run_systolic matmul_qlr_4x2_hybrid                  192   225   192 "square-square_16x16_16x16" "" ""
# dir 5
run_systolic matmul_qlr_4x4_hybrid                  64    930   64  "square-square_16x16_16x16" "" ""
run_systolic matmul_qlr_4x4_hybrid                  320   33    320 "square-square_16x16_16x16" "" ""
run_systolic matmul_qlr_4x4_hybrid                  128   310   192 "square-square_16x16_16x16" "" ""
run_systolic matmul_qlr_4x4_hybrid                  192   225   192 "square-square_16x16_16x16" "" ""
# dir 6
run_systolic matmul_qlr_4x4_hybrid_preload          64    960   60  "square-square_16x16_16x15" "" "" # error!!!!!!
run_systolic matmul_qlr_4x4_hybrid_preload          320   12    360 "square-square_16x16_16x15" "" ""
run_systolic matmul_qlr_4x4_hybrid_preload          128   325   180 "square-square_16x16_16x15" "" ""
run_systolic matmul_qlr_4x4_hybrid_preload          192   240   180 "square-square_16x16_16x15" "" ""
# dir 7
run_systolic matmul_qlr_4x4_hybrid_preload_row      64    960   60  "row-wise_8x32_8x31"        "" "" # stack trace
run_systolic matmul_qlr_4x4_hybrid_preload_row      320   12    360 "row-wise_8x32_8x31"        "" ""
run_systolic matmul_qlr_4x4_hybrid_preload_row      128   325   180 "row-wise_8x32_8x31"        "" ""
run_systolic matmul_qlr_4x4_hybrid_preload_row      192   240   180 "row-wise_8x32_8x31"        "" ""
# dir 8
run_systolic matmul_qlr_4x4_hybrid_preload_row_wide 32    765   124 "row-wise_8x32_8x31"        "" ""
run_systolic matmul_qlr_4x4_hybrid_preload_row_wide 160   30    620 "row-wise_8x32_8x31"        "" "" # gcc error: P > 514
run_systolic matmul_qlr_4x4_hybrid_preload_row_wide 64    345   248 "row-wise_8x32_8x31"        "" ""
run_systolic matmul_qlr_4x4_hybrid_preload_row_wide 128   245   248 "row-wise_8x32_8x31"        "" ""



