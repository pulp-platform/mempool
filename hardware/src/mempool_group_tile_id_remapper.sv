module mempool_group_tile_id_remapper
  import mempool_pkg::*;
  import cf_math_pkg::idx_width;
#(
) (
  input  reqrsp_req_t                                 dma_reqrsp_req_i,
  output logic        [idx_width(NumTilesPerDma)-1:0] tile_id_remap_o
);

  logic        [idx_width(NumTilesPerDma)-1:0] tile_id_remap_before;
  logic        [idx_width(NumTilesPerDma)-1:0] tile_id_remap;
  
  assign tile_id_remap_before = dma_reqrsp_req_i.q.addr[(ByteOffset + idx_width(NumBanksPerTile)) +: idx_width(NumTilesPerDma)];
  assign tile_id_remap        = tile_id_remap_before + 
                                dma_reqrsp_req_i.q.addr[(ByteOffset + idx_width(NumBanksPerTile) + idx_width(NumTilesPerGroup) + idx_width(NumGroups)) +: idx_width(NumTilesPerDma)];

  `ifdef TILE_ID_REMAP
  assign tile_id_remap_o = tile_id_remap;
  `else
  assign tile_id_remap_o = tile_id_remap_before;
  `endif
endmodule