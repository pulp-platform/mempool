// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// One directed link of the inter-Group TCDM network.
//
// The instance routes all TCDM traffic that leaves one Group towards one
// remote Group: the requests issued by the local Tiles, and the responses that
// the local Tiles produce for requests previously received from that remote
// Group. Both directions share a single crossbar, because the underlying
// interconnect is full duplex: the request side carries initiator-to-target
// traffic, the response side carries target-to-initiator traffic.
//
// The link is width preserving. A request enters as a tcdm_master_req_t, whose
// TCDMAddrWidth-wide target address is resolved into a Tile index plus a Tile
// address, and leaves as an equally wide tcdm_slave_req_t. A response enters as
// a tcdm_slave_resp_t, whose Tile identifier selects the initiator, and leaves
// as a tcdm_master_resp_t. This is what makes the module boundary usable as a
// die-to-die cut without inflating the interface.
//
// This logic used to live in the gen_remote_interco generate block of
// mempool_group.

`include "mempool/mempool.svh"

module tensorpool_inter_group_interco
  import mempool_pkg::*;
  import burst_pkg::*;
  import cf_math_pkg::idx_width;
#(
  // Dependent parameter. DO NOT CHANGE.
  parameter int unsigned NumPorts = NumSubGroupsPerGroup * NumTilesPerSubGroup
) (
  input  logic                                                                                  clk_i,
  input  logic                                                                                  rst_ni,
  // Initiator side, towards the local Group
  input  `STRUCT_VECT(tcdm_master_req_t,  [NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0])  tcdm_master_req_i,
  input  logic                            [NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0]   tcdm_master_req_valid_i,
  output logic                            [NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0]   tcdm_master_req_ready_o,
  input  `STRUCT_VECT(tcdm_slave_resp_t,  [NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0])  tcdm_slave_resp_i,
  input  logic                            [NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0]   tcdm_slave_resp_valid_i,
  output logic                            [NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0]   tcdm_slave_resp_ready_o,
  // Target side, towards the remote Group
  output `STRUCT_VECT(tcdm_slave_req_t,   [NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0])  tcdm_slave_req_o,
  output logic                            [NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0]   tcdm_slave_req_valid_o,
  input  logic                            [NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0]   tcdm_slave_req_ready_i,
  output `STRUCT_VECT(tcdm_master_resp_t, [NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0])  tcdm_master_resp_o,
  output logic                            [NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0]   tcdm_master_resp_valid_o,
  input  logic                            [NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0]   tcdm_master_resp_ready_i
);

  /**********************
   *  Ports to structs  *
   **********************/

  // The ports might be structs flattened to vectors. To access the structs'
  // internal signals, assign the flattened vectors back to structs.
  tcdm_master_req_t  [NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_master_req_s;
  tcdm_slave_resp_t  [NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_slave_resp_s;
  tcdm_slave_req_t   [NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_slave_req_s;
  tcdm_master_resp_t [NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_master_resp_s;

  for (genvar sg = 0; sg < NumSubGroupsPerGroup; sg++) begin: gen_tcdm_struct_sg
    assign tcdm_master_req_s[sg]  = tcdm_master_req_i[sg];
    assign tcdm_slave_resp_s[sg]  = tcdm_slave_resp_i[sg];
    assign tcdm_slave_req_o[sg]   = tcdm_slave_req_s[sg];
    assign tcdm_master_resp_o[sg] = tcdm_master_resp_s[sg];
  end: gen_tcdm_struct_sg

  /*****************
   *  Flat arrays  *
   *****************/

  logic           [NumPorts-1:0] master_remote_req_valid;
  logic           [NumPorts-1:0] master_remote_req_ready;
  tcdm_addr_t     [NumPorts-1:0] master_remote_req_tgt_addr;
  logic           [NumPorts-1:0] master_remote_req_wen;
  tcdm_payload_t  [NumPorts-1:0] master_remote_req_wdata;
  strb_t          [NumPorts-1:0] master_remote_req_be;
  burst_t         [NumPorts-1:0] master_remote_req_burst;
  logic           [NumPorts-1:0] master_remote_resp_valid;
  logic           [NumPorts-1:0] master_remote_resp_ready;
  tcdm_payload_t  [NumPorts-1:0] master_remote_resp_rdata;
  burst_gresp_t   [NumPorts-1:0] master_remote_resp_burst;
  logic           [NumPorts-1:0] slave_remote_req_valid;
  logic           [NumPorts-1:0] slave_remote_req_ready;
  tile_addr_t     [NumPorts-1:0] slave_remote_req_tgt_addr;
  tile_group_id_t [NumPorts-1:0] slave_remote_req_tile_id;
  logic           [NumPorts-1:0] slave_remote_req_wen;
  tcdm_payload_t  [NumPorts-1:0] slave_remote_req_wdata;
  strb_t          [NumPorts-1:0] slave_remote_req_be;
  burst_t         [NumPorts-1:0] slave_remote_req_burst;
  logic           [NumPorts-1:0] slave_remote_resp_valid;
  logic           [NumPorts-1:0] slave_remote_resp_ready;
  tile_group_id_t [NumPorts-1:0] slave_remote_resp_tile_id;
  tcdm_payload_t  [NumPorts-1:0] slave_remote_resp_rdata;
  burst_gresp_t   [NumPorts-1:0] slave_remote_resp_burst;

  for (genvar sg = 0; sg < NumSubGroupsPerGroup; sg++) begin: gen_remote_connections_sg
    for (genvar t = 0; t < NumTilesPerSubGroup; t++) begin: gen_remote_connections_t
      assign master_remote_req_valid[(sg * NumTilesPerSubGroup) + t]    = tcdm_master_req_valid_i[sg][t];
      assign master_remote_req_tgt_addr[(sg * NumTilesPerSubGroup) + t] = tcdm_master_req_s[sg][t].tgt_addr;
      assign master_remote_req_wen[(sg * NumTilesPerSubGroup) + t]      = tcdm_master_req_s[sg][t].wen;
      assign master_remote_req_wdata[(sg * NumTilesPerSubGroup) + t]    = tcdm_master_req_s[sg][t].wdata;
      assign master_remote_req_be[(sg * NumTilesPerSubGroup) + t]       = tcdm_master_req_s[sg][t].be;
      assign master_remote_req_burst[(sg * NumTilesPerSubGroup) + t]    = tcdm_master_req_s[sg][t].burst;
      assign tcdm_master_req_ready_o[sg][t]                             = master_remote_req_ready[(sg * NumTilesPerSubGroup) + t];

      assign tcdm_slave_req_valid_o[sg][t]                              = slave_remote_req_valid[(sg * NumTilesPerSubGroup) + t];
      assign tcdm_slave_req_s[sg][t].tgt_addr                           = slave_remote_req_tgt_addr[(sg * NumTilesPerSubGroup) + t];
      assign tcdm_slave_req_s[sg][t].tile_id                            = slave_remote_req_tile_id[(sg * NumTilesPerSubGroup) + t];
      assign tcdm_slave_req_s[sg][t].wen                                = slave_remote_req_wen[(sg * NumTilesPerSubGroup) + t];
      assign tcdm_slave_req_s[sg][t].wdata                              = slave_remote_req_wdata[(sg * NumTilesPerSubGroup) + t];
      assign tcdm_slave_req_s[sg][t].be                                 = slave_remote_req_be[(sg * NumTilesPerSubGroup) + t];
      assign tcdm_slave_req_s[sg][t].burst                              = slave_remote_req_burst[(sg * NumTilesPerSubGroup) + t];
      assign slave_remote_req_ready[(sg * NumTilesPerSubGroup) + t]     = tcdm_slave_req_ready_i[sg][t];

      assign slave_remote_resp_valid[(sg * NumTilesPerSubGroup) + t]    = tcdm_slave_resp_valid_i[sg][t];
      assign slave_remote_resp_tile_id[(sg * NumTilesPerSubGroup) + t]  = tcdm_slave_resp_s[sg][t].tile_id;
      assign slave_remote_resp_rdata[(sg * NumTilesPerSubGroup) + t]    = tcdm_slave_resp_s[sg][t].rdata;
      assign slave_remote_resp_burst[(sg * NumTilesPerSubGroup) + t]    = tcdm_slave_resp_s[sg][t].burst;
      assign tcdm_slave_resp_ready_o[sg][t]                             = slave_remote_resp_ready[(sg * NumTilesPerSubGroup) + t];

      assign tcdm_master_resp_valid_o[sg][t]                            = master_remote_resp_valid[(sg * NumTilesPerSubGroup) + t];
      assign tcdm_master_resp_s[sg][t].rdata                            = master_remote_resp_rdata[(sg * NumTilesPerSubGroup) + t];
      assign tcdm_master_resp_s[sg][t].burst                            = master_remote_resp_burst[(sg * NumTilesPerSubGroup) + t];
      assign master_remote_resp_ready[(sg * NumTilesPerSubGroup) + t]   = tcdm_master_resp_ready_i[sg][t];
    end: gen_remote_connections_t
  end: gen_remote_connections_sg

  /******************
   *  Interconnect  *
   ******************/

  burst_variable_latency_interconnect #(
    .NumIn              (NumPorts                                    ),
    .NumOut             (NumPorts                                    ),
    .AddrWidth          (TCDMAddrWidth                               ),
    .DataWidth          ($bits(tcdm_payload_t)                       ),
    .BeWidth            (DataWidth/8                                 ),
    .BurstWidth         ($bits(burst_t)                              ),
    .BurstRspWidth      ($bits(burst_gresp_t)                        ),
    .ByteOffWidth       (0                                           ),
    .AddrMemWidth       (TCDMAddrMemWidth + idx_width(NumBanksPerTile)),
    .Topology           (tcdm_interconnect_pkg::LIC                  ),
    .AxiVldRdy          (1'b1                                        ),
    .SpillRegisterReq   (64'b1                                       ),
    .SpillRegisterResp  (64'b1                                       ),
    .FallThroughRegister(1'b1                                        )
  ) i_remote_interco (
    .clk_i          (clk_i                     ),
    .rst_ni         (rst_ni                    ),
    .req_valid_i    (master_remote_req_valid   ),
    .req_ready_o    (master_remote_req_ready   ),
    .req_tgt_addr_i (master_remote_req_tgt_addr),
    .req_wen_i      (master_remote_req_wen     ),
    .req_wdata_i    (master_remote_req_wdata   ),
    .req_be_i       (master_remote_req_be      ),
    .req_burst_i    (master_remote_req_burst   ),
    .resp_valid_o   (master_remote_resp_valid  ),
    .resp_ready_i   (master_remote_resp_ready  ),
    .resp_rdata_o   (master_remote_resp_rdata  ),
    .resp_burst_o   (master_remote_resp_burst  ),
    .resp_ini_addr_i(slave_remote_resp_tile_id ),
    .resp_rdata_i   (slave_remote_resp_rdata   ),
    .resp_burst_i   (slave_remote_resp_burst   ),
    .resp_valid_i   (slave_remote_resp_valid   ),
    .resp_ready_o   (slave_remote_resp_ready   ),
    .req_valid_o    (slave_remote_req_valid    ),
    .req_ready_i    (slave_remote_req_ready    ),
    .req_be_o       (slave_remote_req_be       ),
    .req_wdata_o    (slave_remote_req_wdata    ),
    .req_burst_o    (slave_remote_req_burst    ),
    .req_wen_o      (slave_remote_req_wen      ),
    .req_ini_addr_o (slave_remote_req_tile_id  ),
    .req_tgt_addr_o (slave_remote_req_tgt_addr )
  );

endmodule : tensorpool_inter_group_interco
