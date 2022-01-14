#!/usr/bin/env bash

# Copyright 2021 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

i=1
max_attempts=10
while ! memora --ignore-uncommitted-changes "$@"; do
  echo "Attempt $i/$max_attempts of 'memora $@' failed."
  if test $i -ge $max_attempts; then
    echo "'memora $@' keeps failing; aborting!"
    exit 1
  fi
  i=$(($i+1))
done
