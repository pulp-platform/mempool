// Copyright 2021 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Author: Marco Bertuletti <mbertuletti@iis.ee.ethz.ch>
// Slices the addess signal, to index the Tile remote port and local interconnect

module tcdm_addr_slicer
  import mempool_pkg::*;
  import cf_math_pkg::idx_width;
#(
  parameter integer unsigned ByteOffset            = mempool_pkg::ByteOffset,
  parameter integer unsigned TCDMAddrMemWidth      = mempool_pkg::TCDMAddrMemWidth,
  parameter integer unsigned BankAddrWidth         = idx_width(mempool_pkg::NumBanksPerTile),
  parameter integer unsigned TileAddrWidth         = idx_width(mempool_pkg::NumTiles),
  parameter integer unsigned GroupAddrWidth        = idx_width(mempool_pkg::NumGroups),
  parameter integer unsigned GroupTileAddrWidth    = idx_width(mempool_pkg::NumTilesPerGroup),
`ifdef TERAPOOL
  parameter integer unsigned SubGroupTileAddrWidth = idx_width(mempool_pkg::NumTilesPerSubGroup),
  parameter integer unsigned SubGroupAddrWidth     = idx_width(mempool_pkg::NumSubGroupsPerGroup),
`endif
  parameter type remote_sel_t = `ifdef TERAPOOL tile_remote_sel_t `else group_id_t `endif
)(
    input  logic [TileAddrWidth-1:0] tile_id_i,
    input  addr_t                    local_req_tgt_addr_i,
    output tile_addr_t               local_req_tgt_addr_o,
    input  addr_t                    remote_req_tgt_addr_i,
    output tcdm_addr_t               remote_req_tgt_addr_o,
    output remote_sel_t              remote_req_tgt_sel_o
);

  // Addresses in MemPool hierarchies
  logic [TCDMAddrMemWidth-1:0]   row_addr, local_row_addr;
  logic [BankAddrWidth-1:0]      bank_addr, local_bank_addr;
  logic [GroupTileAddrWidth-1:0] g_tile_addr;
  logic [GroupAddrWidth-1:0]     g_addr, remote_req_tgt_g_sel;

`ifdef TERAPOOL
  // Addresses in TeraPool hierarchies
  logic [SubGroupTileAddrWidth-1:0] sg_tile_addr;
  logic [SubGroupAddrWidth-1:0]     sg_addr, remote_req_tgt_sg_sel;
`endif

  // Group ID
  logic [GroupAddrWidth-1:0] group_id;
  assign group_id = (mempool_pkg::NumGroups == 1) ? '0
                  : tile_id_i[TileAddrWidth-1 -: GroupAddrWidth];
`ifdef TERAPOOL
  // SubGroup ID
  logic [SubGroupAddrWidth-1:0] sub_group_id;
  assign sub_group_id = (mempool_pkg::NumSubGroupsPerGroup == 1) ? '0
                      : tile_id_i[TileAddrWidth-GroupAddrWidth-1 -: SubGroupAddrWidth];
`endif

  /********************
   *   Local address  *
   ********************/

  // Remove tile index from local_req_tgt_address_i, since it will not be used for routing.
  assign local_row_addr = local_req_tgt_addr_i[ByteOffset+BankAddrWidth+TileAddrWidth +: TCDMAddrMemWidth];
  assign local_bank_addr = local_req_tgt_addr_i[ByteOffset +: BankAddrWidth];
  assign local_req_tgt_addr_o = tcdm_addr_t'({local_row_addr, local_bank_addr});

`ifdef TERAPOOL

  /*********************
   *   Remote address  *
   *********************/

  if (mempool_pkg::NumTilesPerGroup == 1) begin : gen_remote_req_interco_tgt_addr
    // Switch Tile and bank index
    assign row_addr  = remote_req_tgt_addr_i[ByteOffset+BankAddrWidth+GroupAddrWidth +: TCDMAddrMemWidth];
    assign bank_addr = remote_req_tgt_addr_i[ByteOffset                              +: BankAddrWidth   ];
    assign remote_req_tgt_addr_o = tcdm_addr_t'({row_addr, bank_addr});

  end else begin : gen_remote_req_interco_tgt_addr
    // Switch tile and bank indexes for SubGroup/Group routing, and remove the SubGroup/Group index
    assign row_addr     = remote_req_tgt_addr_i[ByteOffset+BankAddrWidth+GroupTileAddrWidth+GroupAddrWidth +: TCDMAddrMemWidth     ];
    assign bank_addr    = remote_req_tgt_addr_i[ByteOffset                                                 +: BankAddrWidth        ];
    assign sg_tile_addr = remote_req_tgt_addr_i[ByteOffset+BankAddrWidth                                   +: SubGroupTileAddrWidth];
    assign g_tile_addr  = remote_req_tgt_addr_i[ByteOffset+BankAddrWidth                                   +: GroupTileAddrWidth   ];
    assign remote_req_tgt_addr_o = (remote_req_tgt_g_sel == 'b0) ? tcdm_addr_t'({row_addr, bank_addr, sg_tile_addr})
                                                                 : tcdm_addr_t'({row_addr, bank_addr, g_tile_addr});
  end

  /******************************
   *   Remote selection signal  *
   ******************************/

  assign g_addr  = remote_req_tgt_addr_i[ByteOffset+BankAddrWidth+GroupTileAddrWidth    +: GroupAddrWidth   ];
  assign sg_addr = remote_req_tgt_addr_i[ByteOffset+BankAddrWidth+SubGroupTileAddrWidth +: SubGroupAddrWidth];
  assign remote_req_tgt_g_sel  = (g_addr) ^ group_id;
  assign remote_req_tgt_sg_sel = (sg_addr) ^ sub_group_id;

  // Output port depends on target SubGroup
  if ((mempool_pkg::NumGroups == 1) && (mempool_pkg::NumSubGroupsPerGroup == 1)) begin: gen_const_sel
    // Constant selection
    assign remote_req_tgt_sel_o = 1'b0;

  end else if ((mempool_pkg::NumGroups == 1) && (mempool_pkg::NumSubGroupsPerGroup != 1)) begin: gen_sub_group_sel
    // Select only the SubGroup
    assign remote_req_tgt_sel_o = remote_req_tgt_sg_sel;

  end else if ((mempool_pkg::NumGroups != 1) && (mempool_pkg::NumSubGroupsPerGroup == 1)) begin: gen_group_sel
    // Select only the Group
    assign remote_req_tgt_sel_o = remote_req_tgt_g_sel;

  end else if ((mempool_pkg::NumGroups != 1) && (mempool_pkg::NumSubGroupsPerGroup != 1)) begin: gen_remote_sel
    assign remote_req_tgt_sel_o = (remote_req_tgt_g_sel == 'b0) ? remote_req_tgt_sg_sel // Select the SubGroup
                                                                : remote_req_tgt_g_sel + {SubGroupAddrWidth{1'b1}}; // Select the Group
  end

`else

  /*********************
   *   Remote address  *
   *********************/

  if (mempool_pkg::NumTilesPerGroup == 1) begin : gen_remote_req_interco_tgt_addr
    // Switch Tile and bank index
    assign row_addr  = remote_req_tgt_addr_i[ByteOffset+BankAddrWidth+GroupAddrWidth +: TCDMAddrMemWidth];
    assign bank_addr = remote_req_tgt_addr_i[ByteOffset                              +: BankAddrWidth   ];
    assign remote_req_tgt_addr_o = tcdm_addr_t'({row_addr, bank_addr});

  end else begin : gen_remote_req_interco_tgt_addr
    // Switch tile and bank indexes for SubGroup routing, and remove the Group index
    assign row_addr  = remote_req_tgt_addr_i[ByteOffset+BankAddrWidth+GroupTileAddrWidth+GroupAddrWidth +: TCDMAddrMemWidth];
    assign bank_addr = remote_req_tgt_addr_i[ByteOffset                                                 +: BankAddrWidth   ];
    assign g_tile_addr = remote_req_tgt_addr_i[ByteOffset+BankAddrWidth+:GroupTileAddrWidth];
    assign remote_req_tgt_addr_o = tcdm_addr_t'({row_addr, bank_addr, g_tile_addr});
  end

  /******************************
   *   Remote selection signal  *
   ******************************/

  if (mempool_pkg::NumGroups == 1) begin : gen_remote_req_interco_tgt_sel
    // Output port depends on target Group
    assign remote_req_tgt_sel_o = 1'b0;
  end else begin : gen_remote_req_interco_tgt_sel
    // Output port depends on both the target and initiator Group
    assign g_addr = remote_req_tgt_addr_i[ByteOffset+BankAddrWidth+GroupTileAddrWidth+:GroupAddrWidth];
    assign remote_req_tgt_sel_o = (g_addr) ^ group_id;
  end

`endif

endmodule : tcdm_addr_slicer
