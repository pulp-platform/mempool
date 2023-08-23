#!/usr/bin/env bash

# Copyright 2021 ETH Zurich and University of Bologna.
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51

# Author: Sergio Mazzola, ETH Zurich

if [ $(basename "$PWD") != "hardware" ]; then
  echo "ERROR: run this script from the hardware directory"
  exit 1
fi

APP=$1

rm -rf ./build/trace*
mkdir -p ./build

# compile software
make -C ../software/apps systolic/${APP} 2>&1 | tee ./build/gcc.log

# execute simcvcs and parse return status
app=systolic/${APP} make simcvcs 2>&1 | tee ./build/simcvcs.log

RET=$(grep '\[EOC\]' ./build/simcvcs.log | grep -Poh -- '(?<=\(retval = )-?[0-9]+(?=\))')
echo "Parsed return status: $RET"
if [ $RET -ne 0 ]; then
  exit $RET
fi

# parse traces
make trace || exit 1
make tracemac || exit 1

# save results
cd results
DIR=`ls -td -- */ | head -n 1`
mkdir -p ./$DIR/traces
mv ./$DIR/*.trace ./$DIR/traces

mkdir -p ./$DIR/logs
mv ../build/gcc.log ./$DIR/logs
mv ../build/simcvcs.log ./$DIR/logs
git diff > ./$DIR/logs/git_diff.log

mkdir -p ./$DIR/app
cp ../../software/bin/systolic/${APP} ../../software/bin/systolic/${APP}.dump ./$DIR/app
cp ../../software/apps/systolic/${APP}/main.c ../../software/runtime/systolic/${APP}.h ./$DIR/app

mv ../build/tracemac* ./$DIR/

mkdir -p ../../results_journal
mv $DIR ${APP}_${DIR}
mv ${APP}_${DIR} ../../results_journal

cd ..
