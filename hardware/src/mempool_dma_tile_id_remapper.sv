// Copyright 2025 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

module mempool_dma_tile_id_remapper
  import mempool_pkg::*;
  import cf_math_pkg::idx_width;
(
  input  reqrsp_req_t                               dma_reqrsp_req_i,
  output logic [idx_width(NumTilesPerDma)-1:0]      tile_id_remap_o
);

  // Address slice offsets
  localparam int TILE_ID_LOW_OFFSET      = ByteOffset
                                         + idx_width(NumBanksPerTile);
  localparam int TILE_ID_REMAPPED_OFFSET = TILE_ID_LOW_OFFSET
                                         + idx_width(NumTilesPerGroup)
                                         + idx_width(NumGroups);
  localparam int TILE_ID_WIDTH           = idx_width(NumTilesPerDma);

  // Extract fields from address
  logic [TILE_ID_WIDTH-1:0] tile_id_remap_before;
  logic [TILE_ID_WIDTH-1:0] tile_id_remap;

  assign tile_id_remap_before = dma_reqrsp_req_i.q.addr[TILE_ID_LOW_OFFSET +: TILE_ID_WIDTH];
  assign tile_id_remap        = tile_id_remap_before +
                                dma_reqrsp_req_i.q.addr[TILE_ID_REMAPPED_OFFSET +: TILE_ID_WIDTH];

  generate
    if (TileIdRemap == 1) begin : gen_remap_enabled
      always_comb begin
        if (dma_reqrsp_req_i.q.addr < (NumTiles * SeqMemSizePerTile)) begin
          tile_id_remap_o = tile_id_remap_before;
        end else begin
          tile_id_remap_o = tile_id_remap;
        end
      end
    end else begin : gen_remap_disabled
      assign tile_id_remap_o = tile_id_remap_before;
    end
  endgenerate

endmodule
