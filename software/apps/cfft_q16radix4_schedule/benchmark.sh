# Copyright 2022 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
# Author: Marco Bertuletti, ETH Zurich

for a in 1 4 8 16 32 64
do
    cd /scratch2/mbertuletti/mempool/software/apps
    DEFINES+=-DN_FFTs=$a \
    make cfft_q16radix4_schedule
    cd /scratch2/mbertuletti/mempool/hardware
    app=cfft_q16radix4_schedule make buildpath=build_cfft simcvcs
    make buildpath=build_cfft resultpath=result_cfft_terapool_single trace
    cd /scratch2/mbertuletti/mempool/software/apps
done
