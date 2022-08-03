#!/usr/bin/env fish

# Copyright 2021 ETH Zurich and University of Bologna.
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51

for axi_data_width in 512 256 128
  for args in 2,18 4,20 8,24
    echo $args | read -d , dmas_per_group axi_hier_radix
    rm -f build/compilevcs.sh
    for size in 131072 65536 32768 16384 8192 4096 2048 1024
      # DEFINES=-DSIZE=$size make -C ../software/apps memcpy
      # mv ../software/bin/memcpy ../software/bin/memcpy_$size
      echo "axi_data_width=$axi_data_width dmas_per_group=$dmas_per_group axi_hier_radix=$axi_hier_radix" size=$size
      # app=memcpy axi_data_width=$axi_data_width dmas_per_group=$dmas_per_group axi_hier_radix=$axi_hier_radix make sim
      app=memcpy_$size axi_data_width=$axi_data_width dmas_per_group=$dmas_per_group axi_hier_radix=$axi_hier_radix make simcvcs | grep 'Duration'
    end
  end
end
