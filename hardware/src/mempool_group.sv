// Copyright 2021 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "mempool/mempool.svh"
`include "reqrsp_interface/typedef.svh"
`include "common_cells/registers.svh"

module mempool_group
  import mempool_pkg::*;
  import cf_math_pkg::idx_width;
#(
  // TCDM
  parameter addr_t       TCDMBaseAddr = 32'b0,
  // Boot address
  parameter logic [31:0] BootAddr     = 32'h0000_1000
) (
  // Clock and reset
  input  logic                                                    clk_i,
  input  logic                                                    rst_ni,
  input  logic                                                    testmode_i,
  // Scan chain
  input  logic                                                    scan_enable_i,
  input  logic                                                    scan_data_i,
  output logic                                                    scan_data_o,
  // Group ID
  input  logic [idx_width(NumGroups)-1:0]                         group_id_i,
  // TCDM Master interfaces
  output `STRUCT_VECT(tcdm_slave_req_t,   [NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0]) tcdm_master_req_o,
  output logic                            [NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0]  tcdm_master_req_valid_o,
  input  logic                            [NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0]  tcdm_master_req_ready_i,
  input  `STRUCT_VECT(tcdm_master_resp_t, [NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0]) tcdm_master_resp_i,
  input  logic                            [NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0]  tcdm_master_resp_valid_i,
  output logic                            [NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0]  tcdm_master_resp_ready_o,
  // TCDM Slave interfaces
  input  `STRUCT_VECT(tcdm_slave_req_t,   [NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0]) tcdm_slave_req_i,
  input  logic                            [NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0]  tcdm_slave_req_valid_i,
  output logic                            [NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0]  tcdm_slave_req_ready_o,
  output `STRUCT_VECT(tcdm_master_resp_t, [NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0]) tcdm_slave_resp_o,
  output logic                            [NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0]  tcdm_slave_resp_valid_o,
  input  logic                            [NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0]  tcdm_slave_resp_ready_i,
  // Wake up interface
  input  logic                            [NumCoresPerGroup-1:0]                 wake_up_i,
  // RO-Cache configuration
  input  `STRUCT_PORT(ro_cache_ctrl_t)                                           ro_cache_ctrl_i,
  // DMA request
  input  `STRUCT_PORT(dma_req_t)                                                 dma_req_i,
  input  logic                                                                   dma_req_valid_i,
  output logic                                                                   dma_req_ready_o,
  // DMA status
  output `STRUCT_PORT(dma_meta_t)                                                dma_meta_o,
   // AXI Interface
  output `STRUCT_VECT(axi_tile_req_t,     [NumAXIMastersPerGroup-1:0])           axi_mst_req_o,
  input  `STRUCT_VECT(axi_tile_resp_t,    [NumAXIMastersPerGroup-1:0])           axi_mst_resp_i
);

  /*****************
   *  Definitions  *
   *****************/

  typedef logic [idx_width(NumSubGroups)-1:0] sub_group_id_t;

  /*********************
   *  Control Signals  *
   *********************/
  logic [NumCoresPerGroup-1:0] wake_up_q;
  `FF(wake_up_q, wake_up_i, '0, clk_i, rst_ni);

  ro_cache_ctrl_t ro_cache_ctrl_q;
  `FF(ro_cache_ctrl_q, ro_cache_ctrl_i, ro_cache_ctrl_default, clk_i, rst_ni);

  /**********************
   *  Ports to structs  *
   **********************/

  // The ports might be structs flattened to vectors. To access the structs'
  // internal signals, assign the flattened vectors back to structs.
  tcdm_slave_req_t   [NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_master_req_s;
  tcdm_master_resp_t [NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_slave_resp_s;

  for (genvar r = 1; r < NumGroups; r++) begin: gen_tcdm_struct
    assign tcdm_master_req_o[r] = tcdm_master_req_s[r];
    assign tcdm_slave_resp_o[r] = tcdm_slave_resp_s[r];
  end: gen_tcdm_struct

  /****************
   *  Sub_Groups  *
   ****************/

  // TCDM interfaces for groups
  tcdm_master_req_t  [NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_master_req;
  logic              [NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_master_req_valid;
  logic              [NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_master_req_ready;
  tcdm_slave_req_t   [NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_slave_req;
  logic              [NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_slave_req_valid;
  logic              [NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_slave_req_ready;
  tcdm_master_resp_t [NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_master_resp;
  logic              [NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_master_resp_valid;
  logic              [NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_master_resp_ready;
  tcdm_slave_resp_t  [NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_slave_resp;
  logic              [NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_slave_resp_valid;
  logic              [NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_slave_resp_ready;

  // TCDM interfaces for sub_groups
  tcdm_slave_req_t   [NumSubGroupsPerGroup-1:0][NumSubGroupsPerGroup-1:1][NumTilesPerSubGroup-1:0] tcdm_sg_master_req;
  logic              [NumSubGroupsPerGroup-1:0][NumSubGroupsPerGroup-1:1][NumTilesPerSubGroup-1:0] tcdm_sg_master_req_valid;
  logic              [NumSubGroupsPerGroup-1:0][NumSubGroupsPerGroup-1:1][NumTilesPerSubGroup-1:0] tcdm_sg_master_req_ready;
  tcdm_master_resp_t [NumSubGroupsPerGroup-1:0][NumSubGroupsPerGroup-1:1][NumTilesPerSubGroup-1:0] tcdm_sg_master_resp;
  logic              [NumSubGroupsPerGroup-1:0][NumSubGroupsPerGroup-1:1][NumTilesPerSubGroup-1:0] tcdm_sg_master_resp_valid;
  logic              [NumSubGroupsPerGroup-1:0][NumSubGroupsPerGroup-1:1][NumTilesPerSubGroup-1:0] tcdm_sg_master_resp_ready;
  tcdm_slave_req_t   [NumSubGroupsPerGroup-1:0][NumSubGroupsPerGroup-1:1][NumTilesPerSubGroup-1:0] tcdm_sg_slave_req;
  logic              [NumSubGroupsPerGroup-1:0][NumSubGroupsPerGroup-1:1][NumTilesPerSubGroup-1:0] tcdm_sg_slave_req_valid;
  logic              [NumSubGroupsPerGroup-1:0][NumSubGroupsPerGroup-1:1][NumTilesPerSubGroup-1:0] tcdm_sg_slave_req_ready;
  tcdm_master_resp_t [NumSubGroupsPerGroup-1:0][NumSubGroupsPerGroup-1:1][NumTilesPerSubGroup-1:0] tcdm_sg_slave_resp;
  logic              [NumSubGroupsPerGroup-1:0][NumSubGroupsPerGroup-1:1][NumTilesPerSubGroup-1:0] tcdm_sg_slave_resp_valid;
  logic              [NumSubGroupsPerGroup-1:0][NumSubGroupsPerGroup-1:1][NumTilesPerSubGroup-1:0] tcdm_sg_slave_resp_ready;

  // DMA interfaces
  dma_req_t  [NumDmasPerGroup-1:0] dma_req;
  logic      [NumDmasPerGroup-1:0] dma_req_valid;
  logic      [NumDmasPerGroup-1:0] dma_req_ready;
  dma_meta_t [NumDmasPerGroup-1:0] dma_meta;

  // Connect the IOs to the tiles' signals
  assign tcdm_master_resp[NumGroups-1:1]         = tcdm_master_resp_i[NumGroups-1:1];
  assign tcdm_master_resp_valid[NumGroups-1:1]   = tcdm_master_resp_valid_i[NumGroups-1:1];
  assign tcdm_master_resp_ready_o[NumGroups-1:1] = tcdm_master_resp_ready[NumGroups-1:1];
  assign tcdm_slave_req[NumGroups-1:1]           = tcdm_slave_req_i[NumGroups-1:1];
  assign tcdm_slave_req_valid[NumGroups-1:1]     = tcdm_slave_req_valid_i[NumGroups-1:1];
  assign tcdm_slave_req_ready_o[NumGroups-1:1]   = tcdm_slave_req_ready[NumGroups-1:1];

  // AXI interfaces
  axi_tile_req_t   [NumAXIMastersPerGroup-1:0] axi_mst_req;
  axi_tile_resp_t  [NumAXIMastersPerGroup-1:0] axi_mst_resp;

  for (genvar sg = 0; unsigned'(sg) < NumSubGroupsPerGroup; sg++) begin: gen_sub_groups
    sub_group_id_t id;
    assign id = (group_id_i << $clog2(NumSubGroupsPerGroup)) | sg[idx_width(NumSubGroupsPerGroup)-1:0];

    tcdm_master_req_t  [NumGroups-1:1] [NumTilesPerSubGroup-1:0] tran_tcdm_master_req;
    logic              [NumGroups-1:1] [NumTilesPerSubGroup-1:0] tran_tcdm_master_req_valid;
    logic              [NumGroups-1:1] [NumTilesPerSubGroup-1:0] tran_tcdm_master_req_ready;
    tcdm_slave_req_t   [NumGroups-1:1] [NumTilesPerSubGroup-1:0] tran_tcdm_slave_req;
    logic              [NumGroups-1:1] [NumTilesPerSubGroup-1:0] tran_tcdm_slave_req_valid;
    logic              [NumGroups-1:1] [NumTilesPerSubGroup-1:0] tran_tcdm_slave_req_ready;
    tcdm_master_resp_t [NumGroups-1:1] [NumTilesPerSubGroup-1:0] tran_tcdm_master_resp;
    logic              [NumGroups-1:1] [NumTilesPerSubGroup-1:0] tran_tcdm_master_resp_valid;
    logic              [NumGroups-1:1] [NumTilesPerSubGroup-1:0] tran_tcdm_master_resp_ready;
    tcdm_slave_resp_t  [NumGroups-1:1] [NumTilesPerSubGroup-1:0] tran_tcdm_slave_resp;
    logic              [NumGroups-1:1] [NumTilesPerSubGroup-1:0] tran_tcdm_slave_resp_valid;
    logic              [NumGroups-1:1] [NumTilesPerSubGroup-1:0] tran_tcdm_slave_resp_ready;

    mempool_sub_group #(
      .TCDMBaseAddr(TCDMBaseAddr),
      .BootAddr    (BootAddr    )
    ) i_sub_group (
      .clk_i                   (clk_i                                                                 ),
      .rst_ni                  (rst_ni                                                                ),
      .scan_enable_i           (scan_enable_i                                                         ),
      .scan_data_i             (/* Unconnected */                                                     ),
      .scan_data_o             (/* Unconnected */                                                     ),
      .sub_group_id_i          (id                                                                    ),
      // TCDM Master interfaces for groups
      .tcdm_master_req_o       (tran_tcdm_master_req                                                  ),
      .tcdm_master_req_valid_o (tran_tcdm_master_req_valid                                            ),
      .tcdm_master_req_ready_i (tran_tcdm_master_req_ready                                            ),
      .tcdm_master_resp_i      (tran_tcdm_master_resp                                                 ),
      .tcdm_master_resp_valid_i(tran_tcdm_master_resp_valid                                           ),
      .tcdm_master_resp_ready_o(tran_tcdm_master_resp_ready                                           ),
      // TCDM banks interface for groups
      .tcdm_slave_req_i        (tran_tcdm_slave_req                                                   ),
      .tcdm_slave_req_valid_i  (tran_tcdm_slave_req_valid                                             ),
      .tcdm_slave_req_ready_o  (tran_tcdm_slave_req_ready                                             ),
      .tcdm_slave_resp_o       (tran_tcdm_slave_resp                                                  ),
      .tcdm_slave_resp_valid_o (tran_tcdm_slave_resp_valid                                            ),
      .tcdm_slave_resp_ready_i (tran_tcdm_slave_resp_ready                                            ),
      // TCDM Master interfaces for sub_groups
      .tcdm_sg_master_req_o       (tcdm_sg_master_req[sg]                                             ),
      .tcdm_sg_master_req_valid_o (tcdm_sg_master_req_valid[sg]                                       ),
      .tcdm_sg_master_req_ready_i (tcdm_sg_master_req_ready[sg]                                       ),
      .tcdm_sg_master_resp_i      (tcdm_sg_master_resp[sg]                                            ),
      .tcdm_sg_master_resp_valid_i(tcdm_sg_master_resp_valid[sg]                                      ),
      .tcdm_sg_master_resp_ready_o(tcdm_sg_master_resp_ready[sg]                                      ),
      // TCDM banks interface for sub_groups
      .tcdm_sg_slave_req_i        (tcdm_sg_slave_req[sg]                                              ),
      .tcdm_sg_slave_req_valid_i  (tcdm_sg_slave_req_valid[sg]                                        ),
      .tcdm_sg_slave_req_ready_o  (tcdm_sg_slave_req_ready[sg]                                        ),
      .tcdm_sg_slave_resp_o       (tcdm_sg_slave_resp[sg]                                             ),
      .tcdm_sg_slave_resp_valid_o (tcdm_sg_slave_resp_valid[sg]                                       ),
      .tcdm_sg_slave_resp_ready_i (tcdm_sg_slave_resp_ready[sg]                                       ),
      // DMA interfaces
      .dma_req_i               (dma_req[sg*NumDmasPerSubGroup +: NumDmasPerSubGroup]                  ),
      .dma_req_valid_i         (dma_req_valid[sg*NumDmasPerSubGroup +: NumDmasPerSubGroup]            ),
      .dma_req_ready_o         (dma_req_ready[sg*NumDmasPerSubGroup +: NumDmasPerSubGroup]            ),
      .dma_meta_o              (dma_meta[sg*NumDmasPerSubGroup +: NumDmasPerSubGroup]                 ),
      // AXI interface
      .axi_mst_req_o           (axi_mst_req[sg*NumAXIMastersPerSubGroup +: NumAXIMastersPerSubGroup]  ),
      .axi_mst_resp_i          (axi_mst_resp[sg*NumAXIMastersPerSubGroup +: NumAXIMastersPerSubGroup] ),
      // RO-Cache configuration
      .ro_cache_ctrl_i         (ro_cache_ctrl_q                                                       ),
      // Wake up interface
      .wake_up_i      (wake_up_q[sg*NumCoresPerSubGroup +: NumCoresPerSubGroup]                       )
    );

    // Transpose the group requests
    for (genvar g = 1; g < NumGroups; g++) begin: gen_tran_group_req
      assign tcdm_master_req[g][sg]         = tran_tcdm_master_req[g];
      assign tcdm_master_req_valid[g][sg]   = tran_tcdm_master_req_valid[g];
      assign tran_tcdm_master_req_ready[g]  = tcdm_master_req_ready[g][sg];
      assign tran_tcdm_master_resp[g]       = tcdm_master_resp[g][sg];
      assign tran_tcdm_master_resp_valid[g] = tcdm_master_resp_valid[g][sg];
      assign tcdm_master_resp_ready[g][sg]  = tran_tcdm_master_resp_ready[g];
      assign tran_tcdm_slave_req[g]         = tcdm_slave_req[g][sg];
      assign tran_tcdm_slave_req_valid[g]   = tcdm_slave_req_valid[g][sg];
      assign tcdm_slave_req_ready[g][sg]    = tran_tcdm_slave_req_ready[g];
      assign tcdm_slave_resp[g][sg]         = tran_tcdm_slave_resp[g];
      assign tcdm_slave_resp_valid[g][sg]   = tran_tcdm_slave_resp_valid[g];
      assign tran_tcdm_slave_resp_ready[g]  = tcdm_slave_resp_ready[g][sg];
    end: gen_tran_group_req
  end : gen_sub_groups

  /******************************
   *  Sub_Groups Interconnects  *
   *****************************/

  for (genvar ini = 0; ini < NumSubGroupsPerGroup; ini++) begin: gen_sg_interconnections_ini
    for (genvar tgt = 0; tgt < NumSubGroupsPerGroup; tgt++) begin: gen_sg_interconnections_tgt
      // The local connections are inside the groups
      if (ini != tgt) begin: gen_remote_sg_interconnections
        assign tcdm_sg_slave_req[tgt][ini ^ tgt]         = tcdm_sg_master_req[ini][ini ^ tgt];
        assign tcdm_sg_slave_req_valid[tgt][ini ^ tgt]   = tcdm_sg_master_req_valid[ini][ini ^ tgt];
        assign tcdm_sg_master_req_ready[ini][ini ^ tgt]  = tcdm_sg_slave_req_ready[tgt][ini ^ tgt];
        assign tcdm_sg_master_resp[tgt][ini ^ tgt]       = tcdm_sg_slave_resp[ini][ini ^ tgt];
        assign tcdm_sg_master_resp_valid[tgt][ini ^ tgt] = tcdm_sg_slave_resp_valid[ini][ini ^ tgt];
        assign tcdm_sg_slave_resp_ready[ini][ini ^ tgt]  = tcdm_sg_master_resp_ready[tgt][ini ^ tgt];
      end: gen_remote_sg_interconnections
    end: gen_sg_interconnections_tgt
  end: gen_sg_interconnections_ini

  /********************************
   *  Remote Group Interconnects  *
   ********************************/

  for (genvar r = 1; r < NumGroups; r++) begin: gen_remote_interco
    logic           [(NumSubGroupsPerGroup * NumTilesPerSubGroup)-1:0] master_remote_req_valid;
    logic           [(NumSubGroupsPerGroup * NumTilesPerSubGroup)-1:0] master_remote_req_ready;
    tcdm_addr_t     [(NumSubGroupsPerGroup * NumTilesPerSubGroup)-1:0] master_remote_req_tgt_addr;
    logic           [(NumSubGroupsPerGroup * NumTilesPerSubGroup)-1:0] master_remote_req_wen;
    tcdm_payload_t  [(NumSubGroupsPerGroup * NumTilesPerSubGroup)-1:0] master_remote_req_wdata;
    strb_t          [(NumSubGroupsPerGroup * NumTilesPerSubGroup)-1:0] master_remote_req_be;
    logic           [(NumSubGroupsPerGroup * NumTilesPerSubGroup)-1:0] master_remote_resp_valid;
    logic           [(NumSubGroupsPerGroup * NumTilesPerSubGroup)-1:0] master_remote_resp_ready;
    tcdm_payload_t  [(NumSubGroupsPerGroup * NumTilesPerSubGroup)-1:0] master_remote_resp_rdata;
    logic           [(NumSubGroupsPerGroup * NumTilesPerSubGroup)-1:0] slave_remote_req_valid;
    logic           [(NumSubGroupsPerGroup * NumTilesPerSubGroup)-1:0] slave_remote_req_ready;
    tile_addr_t     [(NumSubGroupsPerGroup * NumTilesPerSubGroup)-1:0] slave_remote_req_tgt_addr;
    tile_group_id_t [(NumSubGroupsPerGroup * NumTilesPerSubGroup)-1:0] slave_remote_req_ini_addr;
    logic           [(NumSubGroupsPerGroup * NumTilesPerSubGroup)-1:0] slave_remote_req_wen;
    tcdm_payload_t  [(NumSubGroupsPerGroup * NumTilesPerSubGroup)-1:0] slave_remote_req_wdata;
    strb_t          [(NumSubGroupsPerGroup * NumTilesPerSubGroup)-1:0] slave_remote_req_be;
    logic           [(NumSubGroupsPerGroup * NumTilesPerSubGroup)-1:0] slave_remote_resp_valid;
    logic           [(NumSubGroupsPerGroup * NumTilesPerSubGroup)-1:0] slave_remote_resp_ready;
    tile_group_id_t [(NumSubGroupsPerGroup * NumTilesPerSubGroup)-1:0] slave_remote_resp_ini_addr;
    tcdm_payload_t  [(NumSubGroupsPerGroup * NumTilesPerSubGroup)-1:0] slave_remote_resp_rdata;

    for (genvar sg = 0; sg < NumSubGroupsPerGroup; sg++) begin: gen_remote_connections_sg
      for (genvar t = 0; t < NumTilesPerSubGroup; t++) begin: gen_remote_connections_t
        assign master_remote_req_valid[(sg * NumTilesPerSubGroup) + t]    = tcdm_master_req_valid[r][sg][t];
        assign master_remote_req_tgt_addr[(sg * NumTilesPerSubGroup) + t] = tcdm_master_req[r][sg][t].tgt_addr;
        assign master_remote_req_wen[(sg * NumTilesPerSubGroup) + t]      = tcdm_master_req[r][sg][t].wen;
        assign master_remote_req_wdata[(sg * NumTilesPerSubGroup) + t]    = tcdm_master_req[r][sg][t].wdata;
        assign master_remote_req_be[(sg * NumTilesPerSubGroup) + t]       = tcdm_master_req[r][sg][t].be;
        assign tcdm_master_req_ready[r][sg][t]                            = master_remote_req_ready[(sg * NumTilesPerSubGroup) + t];
        assign tcdm_master_req_valid_o[r][sg][t]                          = slave_remote_req_valid[(sg * NumTilesPerSubGroup) + t];
        assign tcdm_master_req_s[r][sg][t].tgt_addr                       = slave_remote_req_tgt_addr[(sg * NumTilesPerSubGroup) + t];
        assign tcdm_master_req_s[r][sg][t].ini_addr                       = slave_remote_req_ini_addr[(sg * NumTilesPerSubGroup) + t];
        assign tcdm_master_req_s[r][sg][t].wen                            = slave_remote_req_wen[(sg * NumTilesPerSubGroup) + t];
        assign tcdm_master_req_s[r][sg][t].wdata                          = slave_remote_req_wdata[(sg * NumTilesPerSubGroup) + t];
        assign tcdm_master_req_s[r][sg][t].be                             = slave_remote_req_be[(sg * NumTilesPerSubGroup) + t];
        assign slave_remote_req_ready[(sg * NumTilesPerSubGroup) + t]     = tcdm_master_req_ready_i[r][sg][t];
        assign slave_remote_resp_valid[(sg * NumTilesPerSubGroup) + t]    = tcdm_slave_resp_valid[r][sg][t];
        assign slave_remote_resp_ini_addr[(sg * NumTilesPerSubGroup) + t] = tcdm_slave_resp[r][sg][t].ini_addr;
        assign slave_remote_resp_rdata[(sg * NumTilesPerSubGroup) + t]    = tcdm_slave_resp[r][sg][t].rdata;
        assign tcdm_slave_resp_ready[r][sg][t]                            = slave_remote_resp_ready[(sg * NumTilesPerSubGroup) + t];
        assign tcdm_slave_resp_valid_o[r][sg][t]                          = master_remote_resp_valid[(sg * NumTilesPerSubGroup) + t];
        assign tcdm_slave_resp_s[r][sg][t].rdata                          = master_remote_resp_rdata[(sg * NumTilesPerSubGroup) + t];
        assign master_remote_resp_ready[(sg * NumTilesPerSubGroup) + t]   = tcdm_slave_resp_ready_i[r][sg][t];
      end: gen_remote_connections_t
    end: gen_remote_connections_sg

    variable_latency_interconnect #(
      .NumIn              (NumSubGroupsPerGroup * NumTilesPerSubGroup   ),
      .NumOut             (NumSubGroupsPerGroup * NumTilesPerSubGroup   ),
      .AddrWidth          (TCDMAddrWidth                                ),
      .DataWidth          ($bits(tcdm_payload_t)                        ),
      .BeWidth            (DataWidth/8                                  ),
      .ByteOffWidth       (0                                            ),
      .AddrMemWidth       (TCDMAddrMemWidth + idx_width(NumBanksPerTile)),
      .Topology           (tcdm_interconnect_pkg::LIC                   ),
      .AxiVldRdy          (1'b1                                         ),
      .SpillRegisterReq   (64'b1                                        ),
      .SpillRegisterResp  (64'b1                                        ),
      .FallThroughRegister(1'b1                                         )
    ) i_remote_interco (
      .clk_i          (clk_i                     ),
      .rst_ni         (rst_ni                    ),
      .req_valid_i    (master_remote_req_valid   ),
      .req_ready_o    (master_remote_req_ready   ),
      .req_tgt_addr_i (master_remote_req_tgt_addr),
      .req_wen_i      (master_remote_req_wen     ),
      .req_wdata_i    (master_remote_req_wdata   ),
      .req_be_i       (master_remote_req_be      ),
      .resp_valid_o   (master_remote_resp_valid  ),
      .resp_ready_i   (master_remote_resp_ready  ),
      .resp_rdata_o   (master_remote_resp_rdata  ),
      .resp_ini_addr_i(slave_remote_resp_ini_addr),
      .resp_rdata_i   (slave_remote_resp_rdata   ),
      .resp_valid_i   (slave_remote_resp_valid   ),
      .resp_ready_o   (slave_remote_resp_ready   ),
      .req_valid_o    (slave_remote_req_valid    ),
      .req_ready_i    (slave_remote_req_ready    ),
      .req_be_o       (slave_remote_req_be       ),
      .req_wdata_o    (slave_remote_req_wdata    ),
      .req_wen_o      (slave_remote_req_wen      ),
      .req_ini_addr_o (slave_remote_req_ini_addr ),
      .req_tgt_addr_o (slave_remote_req_tgt_addr )
    );

  end: gen_remote_interco

  /**********************
   *    AXI Register    *
   **********************/

  for (genvar m = 0; m < NumAXIMastersPerGroup; m++) begin: gen_axi_group_cuts
    axi_cut #(
      .ar_chan_t (axi_tile_ar_t  ),
      .aw_chan_t (axi_tile_aw_t  ),
      .r_chan_t  (axi_tile_r_t   ),
      .w_chan_t  (axi_tile_w_t   ),
      .b_chan_t  (axi_tile_b_t   ),
      .axi_req_t (axi_tile_req_t ),
      .axi_resp_t(axi_tile_resp_t)
    ) i_axi_cut (
      .clk_i     (clk_i            ),
      .rst_ni    (rst_ni           ),
      .slv_req_i (axi_mst_req[m]   ),
      .slv_resp_o(axi_mst_resp[m]  ),
      .mst_req_o (axi_mst_req_o[m] ),
      .mst_resp_i(axi_mst_resp_i[m])
    );
  end: gen_axi_group_cuts

  /********************
   *  DMA Distribute  *
   ********************/
  dma_req_t  dma_req_cut;
  logic      dma_req_cut_valid;
  logic      dma_req_cut_ready;
  dma_meta_t dma_meta_cut;

  spill_register #(
    .T(dma_req_t)
  ) i_dma_req_register (
    .clk_i  (clk_i            ),
    .rst_ni (rst_ni           ),
    .data_i (dma_req_i        ),
    .valid_i(dma_req_valid_i  ),
    .ready_o(dma_req_ready_o  ),
    .data_o (dma_req_cut      ),
    .valid_o(dma_req_cut_valid),
    .ready_i(dma_req_cut_ready)
  );

  `FF(dma_meta_o, dma_meta_cut, '0, clk_i, rst_ni);

  idma_distributed_midend #(
    .NoMstPorts     (NumDmasPerGroup                         ),
    .DmaRegionWidth (NumBanksPerGroup*4/NumDmasPerGroup      ),
    .DmaRegionStart (TCDMBaseAddr                            ),
    .DmaRegionEnd   (TCDMBaseAddr+TCDMSize                   ),
    .TransFifoDepth (8                                       ),
    .burst_req_t    (dma_req_t                               ),
    .meta_t         (dma_meta_t                              )
  ) i_idma_distributed_midend (
    .clk_i       (clk_i            ),
    .rst_ni      (rst_ni           ),
    .burst_req_i (dma_req_cut      ),
    .valid_i     (dma_req_cut_valid),
    .ready_o     (dma_req_cut_ready),
    .meta_o      (dma_meta_cut     ),
    .burst_req_o (dma_req          ),
    .valid_o     (dma_req_valid    ),
    .ready_i     (dma_req_ready    ),
    .meta_i      (dma_meta         )
  );

endmodule : mempool_group
