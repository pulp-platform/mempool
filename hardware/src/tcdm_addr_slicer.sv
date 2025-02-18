// Copyright 2021 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Author: Marco Bertuletti <mbertuletti@iis.ee.ethz.ch>
// Slices the addess signal, to index the Tile remote port and local interconnect

module tcdm_addr_slicer
  import mempool_pkg::*;
  import cf_math_pkg::idx_width;
(
  // Local request
  input   addr_t        local_req_tgt_address_i,
  output  tile_addr_t   local_req_tgt_address_o,
  // Remote request
  input   addr_t        remote_req_tgt_addr_i,
  output  tcdm_addr_t   remote_req_tgt_addr_o,
  input  logic          [idx_width(NumTiles)-1:0] tile_id_i,
  `ifdef TERAPOOL
    output tile_remote_sel_t  remote_req_tgt_sel_o
  `else
    output group_id_t         remote_req_tgt_sel_o
  `endif
);

  logic [TCDMAddrMemWidth-1:0] local_row_addr;
  logic [$clog2(NumBanksPerTile)-1:0] local_bank_addr;

  logic [TCDMAddrMemWidth-1:0] row_addr;
  logic [$clog2(NumBanksPerTile)-1:0] bank_addr;
  logic [$clog2(NumTilesPerGroup)-1:0] g_tile_addr;

  logic [$clog2(NumGroups)-1:0] g_addr;
  logic [$clog2(NumGroups)-1:0] remote_req_tgt_g_sel;

`ifdef TERAPOOL
  logic [$clog2(NumTilesPerSubGroup)-1:0] sg_tile_addr;
  logic [$clog2(NumSubGroupsPerGroup)-1:0] sg_addr;
  logic [$clog2(NumSubGroupsPerGroup)-1:0] remote_req_tgt_sg_sel;
`endif

  // Group ID
  logic [idx_width(NumGroups)-1:0] group_id;
  if (NumGroups != 1) begin: gen_group_id
    assign group_id = tile_id_i[$clog2(NumTiles)-1 -: $clog2(NumGroups)];
  end else begin: gen_group_id
    assign group_id = '0;
  end: gen_group_id

  `ifdef TERAPOOL
    // SubGroup ID
    logic [idx_width(NumSubGroupsPerGroup)-1:0] sub_group_id;
    if (NumSubGroupsPerGroup != 1) begin: gen_sub_group_id
      assign sub_group_id = tile_id_i[$clog2(NumTiles)-$clog2(NumGroups)-1 -: $clog2(NumSubGroupsPerGroup)];
    end else begin: gen_sub_group_id
      assign sub_group_id = '0;
    end: gen_sub_group_id
  `endif

  /*********************
   *   Local address  *
   *********************/

  // Remove tile index from local_req_tgt_address_i, since it will not be used for routing.
  assign local_row_addr = local_req_tgt_address_i[ByteOffset + $clog2(NumBanksPerTile) + $clog2(NumTiles) +: TCDMAddrMemWidth];
  assign local_bank_addr = local_req_tgt_address_i[ByteOffset +: $clog2(NumBanksPerTile)];
  assign local_req_tgt_address_o = tcdm_addr_t'({row_addr, bank_addr});

`ifdef TERAPOOL

  /*********************
   *   Remote address  *
   *********************/

  if (NumTilesPerGroup == 1) begin : gen_remote_req_interco_tgt_addr
    // Switch Tile and bank index
    assign row_addr = remote_req_tgt_addr_i[ByteOffset + $clog2(NumBanksPerTile) + $clog2(NumGroups) +: TCDMAddrMemWidth];
    assign bank_addr = remote_req_tgt_addr_i[ByteOffset +: $clog2(NumBanksPerTile)];
    assign remote_req_tgt_addr_o = tcdm_addr_t'({row_addr, bank_addr});

  end else begin : gen_remote_req_interco_tgt_addr
    always_comb begin
      if (remote_req_tgt_g_sel == 'b0) begin
        // Switch tile and bank indexes for SubGroup routing, and remove the SubGroup index
        row_addr = remote_req_tgt_addr_i[ByteOffset + $clog2(NumBanksPerTile) + $clog2(NumTilesPerGroup) + $clog2(NumGroups) +: TCDMAddrMemWidth];
        bank_addr = remote_req_tgt_addr_i[ByteOffset +: $clog2(NumBanksPerTile)];
        sg_tile_addr = remote_req_tgt_addr_i[ByteOffset + $clog2(NumBanksPerTile) +: $clog2(NumTilesPerSubGroup)];
        remote_req_tgt_addr_o = tcdm_addr_t'({row_addr, bank_addr, sg_tile_addr});
      end else begin
        // Switch tile and bank indexes for Group routing, and remove the Group index
        row_addr = remote_req_tgt_addr_i[ByteOffset + $clog2(NumBanksPerTile) + $clog2(NumTilesPerGroup) + $clog2(NumGroups) +: TCDMAddrMemWidth];
        bank_addr = remote_req_tgt_addr_i[ByteOffset +: $clog2(NumBanksPerTile)];
        g_tile_addr = remote_req_tgt_addr_i[ByteOffset + $clog2(NumBanksPerTile) +: $clog2(NumTilesPerGroup)];
        remote_req_tgt_addr_o = tcdm_addr_t'({row_addr, bank_addr, g_tile_addr});
      end
    end
  end

  /******************************
   *   Remote selection signal  *
   ******************************/

  assign g_addr = remote_req_tgt_addr_i[ByteOffset + $clog2(NumBanksPerTile) + $clog2(NumTilesPerGroup) +: $clog2(NumGroups)];
  assign sg_addr = remote_req_tgt_addr_i[ByteOffset + $clog2(NumBanksPerTile) + $clog2(NumTilesPerSubGroup) +: $clog2(NumSubGroupsPerGroup)];

  // Output port depends on target SubGroup
  if (NumGroups == 1) begin : gen_remote_req_interco_tgt_sel

    // Select SubGroup index
    if (NumSubGroupsPerGroup == 1) begin : gen_const_sel
      assign remote_req_tgt_sel_o = 1'b0;
    end else begin : gen_const_sel
      assign remote_req_tgt_sel_o = (sg_addr) ^ sub_group_id;
    end

  // Output port depends on both the target and initiator Group & SubGroup
  end else begin : gen_remote_req_interco_tgt_sel

    if (NumSubGroupsPerGroup == 1) begin : gen_remote_group_sel
      // Only select the Group
      assign remote_req_tgt_sel_o = (g_addr) ^ group_id;

    end else begin : gen_remote_group_sel
      // Select the Group
      assign remote_req_tgt_g_sel  = (g_addr) ^ group_id;
      assign remote_req_tgt_sg_sel = (sg_addr) ^ sub_group_id;
      // Select the SubGroup
      always_comb begin : gen_remote_sub_group_sel
        if (remote_req_tgt_g_sel == 'b0) begin: gen_local_group_sel
          remote_req_tgt_sel_o = remote_req_tgt_sg_sel;
        end else begin: gen_remote_group_sel
          remote_req_tgt_sel_o = remote_req_tgt_g_sel + {(idx_width(NumSubGroupsPerGroup)){1'b1}};
        end
      end

    end
  end

`else

  /*********************
   *   Remote address  *
   *********************/

  if (NumTilesPerGroup == 1) begin : gen_remote_req_interco_tgt_addr
    // Switch Tile and bank index
    assign row_addr = remote_req_tgt_addr_i[ByteOffset + $clog2(NumBanksPerTile) + $clog2(NumGroups) +: TCDMAddrMemWidth];
    assign bank_addr = remote_req_tgt_addr_i[ByteOffset +: $clog2(NumBanksPerTile)];
    assign remote_req_tgt_addr_o = tcdm_addr_t'({row_addr, bank_addr});

  end else begin : gen_remote_req_interco_tgt_addr
    // Switch tile and bank indexes for SubGroup routing, and remove the Group index
    assign row_addr = remote_req_tgt_addr_i[ByteOffset + $clog2(NumBanksPerTile) + $clog2(NumTilesPerGroup) + $clog2(NumGroups) +: TCDMAddrMemWidth];
    assign bank_addr = remote_req_tgt_addr_i[ByteOffset +: $clog2(NumBanksPerTile)];
    assign g_tile_addr = remote_req_tgt_addr_i[ByteOffset + $clog2(NumBanksPerTile) +: $clog2(NumTilesPerGroup)];
    assign remote_req_tgt_addr_o = tcdm_addr_t'({row_addr, bank_addr, g_tile_addr});
  end

  /******************************
   *   Remote selection signal  *
   ******************************/

  if (NumGroups == 1) begin : gen_remote_req_interco_tgt_sel
    // Output port depends on target Group
    assign remote_req_tgt_sel_o = 1'b0;
  end else begin : gen_remote_req_interco_tgt_sel
    // Output port depends on both the target and initiator Group
    assign g_addr = remote_req_tgt_addr_i[ByteOffset + $clog2(NumBanksPerTile) + $clog2(NumTilesPerGroup) +: $clog2(NumGroups)];
    assign remote_req_tgt_sel_o = (g_addr) ^ group_id;
  end

`endif

endmodule : tcdm_addr_slicer
