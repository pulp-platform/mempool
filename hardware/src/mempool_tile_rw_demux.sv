// Copyright 2021 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "mempool/mempool.svh"

module mempool_tile_rw_demux
  import mempool_pkg::*;
  import cf_math_pkg::idx_width;
#(
  parameter int unsigned NumCoresPerTile              = 4,
  parameter int unsigned NumRemoteReqPortsPerTile     = 4,
  parameter int unsigned NumRdRemoteReqPortsPerTile   = 2,
  parameter int unsigned NumWrRemoteReqPortsPerTile   = 2,
  parameter int unsigned NumWideRemoteReqPortsPerTile = 0,
  parameter int unsigned NumRdWrRemoteReqPortsPerTile = 0,
  parameter int unsigned NumBanksPerTile              = 16,
  parameter int unsigned NumTilesPerGroup             = 4,
  parameter int unsigned NumGroups                    = 4,
  parameter int unsigned ByteOffset                   = 2
) (
  input  group_id_t                                                           group_id_i,
  input  logic                [NumCoresPerTile-1:0]                           remote_req_interco_valid_i,
  input  logic                [NumCoresPerTile-1:0]                           remote_req_interco_ready_i,
  input  logic                [NumCoresPerTile-1:0]                           remote_req_interco_wen_i,
  input  logic                [NumCoresPerTile-1:0]                           remote_req_interco_amoen_i,
  input  addr_t               [NumCoresPerTile-1:0]                           prescramble_tcdm_req_tgt_addr_i,
  output logic                [NumCoresPerTile-1:0]                           remote_req_interco_to_xbar_valid_o,
  output logic                [NumCoresPerTile-1:0]                           remote_req_interco_to_xbar_ready_o,
  output logic [NumCoresPerTile-1:0][idx_width(NumRemoteReqPortsPerTile)-1:0] remote_req_interco_tgt_sel_o
);

  /*******************
   *   Core De/mux   *
   *******************/
  group_id_t           [NumCoresPerTile-1:0]                    tgt_group_id;
  logic                [NumCoresPerTile-1:0]                    group_id_is_local;

  for (genvar c = 0; c < NumCoresPerTile; c++) begin: gen_core_mux
    assign tgt_group_id[c] = prescramble_tcdm_req_tgt_addr_i[c][ByteOffset + $clog2(NumBanksPerTile) + $clog2(NumTilesPerGroup) +: $clog2(NumGroups)];
    assign group_id_is_local[c] = tgt_group_id[c] == group_id_i;

    // Map the requests from cores to the
    // channels with different usage:
    //                                 port id
    // ------     ------   -> local    [ 0 (lsb for local port)
    // |    | ->  |    |   -> r     Low  1
    // |Tile| ->  |xbar|   -> r     ||   2
    // |    | ->  |    |   -> rw    ||   3
    // |    | ->  |    |   -> w     \/   4
    // ------     ------   -> w    High   5 ]

    if((NumRdRemoteReqPortsPerTile > 0) || (NumWrRemoteReqPortsPerTile > 0)) begin
      assign remote_req_interco_tgt_sel_o[c] = group_id_is_local[c] ? 0 :
                                              ~(remote_req_interco_wen_i[c] | remote_req_interco_amoen_i[c]) ?
                                               (1 + (c % (NumRdRemoteReqPortsPerTile + NumRdWrRemoteReqPortsPerTile))) :
                                               (1 + NumRdRemoteReqPortsPerTile + (c % (NumWideRemoteReqPortsPerTile)));
    end else begin
      assign remote_req_interco_tgt_sel_o[c] = group_id_is_local[c] ? 0 : (1 + (c % (NumRemoteReqPortsPerTile - 1)));
    end
  end

  assign remote_req_interco_to_xbar_valid_o   = remote_req_interco_valid_i;
  assign remote_req_interco_to_xbar_ready_o   = remote_req_interco_ready_i;
endmodule
