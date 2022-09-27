# Copyright 2021 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Author: Marco Bertuletti, ETH Zurich

for a in 8 16 32 64
do
    cd /scratch2/mbertuletti/mempool/software/apps
    DEFINES+=-DN=$a \
    make choldec
    cd /scratch2/mbertuletti/mempool/hardware
    app=choldec make buildpath=build_choldec simcvcs
    make buildpath=build_choldec resultpath=results_choldec_parallel trace
    cd /scratch2/mbertuletti/mempool/software/apps
done
