#!/usr/bin/env fish

# Copyright 2021 ETH Zurich and University of Bologna.
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51

mkdir -p build

for axi_data_width in 512 256 128
  for args in 1,17 2,18 4,20 8,24 16,32
    echo $args | read -d , dmas_per_group axi_hier_radix
    rm -f build/compilevcs.sh
    for size in 131072 65536 32768 16384 8192 4096 2048 1024
      # DEFINES=-DSIZE=$size make -C ../software/apps memcpy
      # mv ../software/bin/memcpy ../software/bin/memcpy_$size
      # mv ../software/bin/memcpy.dump ../software/bin/memcpy_$size.dump
      echo "app=memcpy_$size axi_data_width=$axi_data_width ro_line_width=$axi_data_width dmas_per_group=$dmas_per_group axi_hier_radix=$axi_hier_radix"
      set suffix {$size}_{$axi_data_width}_{$dmas_per_group}
      app=memcpy_$size axi_data_width=$axi_data_width ro_line_width=$axi_data_width dmas_per_group=$dmas_per_group axi_hier_radix=$axi_hier_radix timeout 10m make simcvcs | tee build/transcript_$suffix | grep -i 'fatal'
      grep 'Duration' build/dma.log
      mv build/dma.log build/dma_$suffix.log
    end
  end
end
