// Copyright 2021 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "common_cells/registers.svh"

module terapool_upper_die
  import mempool_pkg::*;
  import cf_math_pkg::idx_width;
#(
  // TCDM
  parameter addr_t                 TCDMBaseAddr  = 32'b0,
  // Boot address
  parameter logic           [31:0] BootAddr      = 32'h0000_0000,
  // Dependant parameters. DO NOT CHANGE!
  parameter int    unsigned        NumDMAReq     = NumGroups * NumDmasPerGroup,
  parameter int    unsigned        NumAXIMasters = NumGroups * NumAXIMastersPerGroup
) (
  // Clock and reset
  input  logic                                                                                                  clk_i,
  input  logic                                                                                                  rst_ni,
  input  logic                                                                                                  testmode_i,
  // Scan chain
  input  logic                                                                                                  scan_enable_i,
  input  logic                                                                                                  scan_data_i,
  output logic                                                                                                  scan_data_o,

  // TCDM master request
  output tcdm_slave_req_t   [NumGroups/2-1:0][NumGroups/2-1:0][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_master_req_o,
  output logic              [NumGroups/2-1:0][NumGroups/2-1:0][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_master_req_valid_o,
  input  logic              [NumGroups/2-1:0][NumGroups/2-1:0][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_master_req_ready_i,
  input  tcdm_slave_req_t   [NumGroups/2-1:0][NumGroups-1:NumGroups/2][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_master_req_i,
  input  logic              [NumGroups/2-1:0][NumGroups-1:NumGroups/2][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_master_req_valid_i,
  output logic              [NumGroups/2-1:0][NumGroups-1:NumGroups/2][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_master_req_ready_o,
  
  // TCDM slave response
  input  tcdm_master_resp_t [NumGroups/2-1:0][NumGroups-1:NumGroups/2][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_slave_resp_i,
  input  logic              [NumGroups/2-1:0][NumGroups-1:NumGroups/2][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_slave_resp_valid_i,
  output logic              [NumGroups/2-1:0][NumGroups-1:NumGroups/2][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_slave_resp_ready_o,
  output tcdm_master_resp_t [NumGroups/2-1:0][NumGroups/2-1:0][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_slave_resp_o,
  output logic              [NumGroups/2-1:0][NumGroups/2-1:0][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_slave_resp_valid_o,
  input  logic              [NumGroups/2-1:0][NumGroups/2-1:0][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_slave_resp_ready_i,

  // Wake up signal
  input  logic              [NumCores/2-1:0]                                                                    wake_up_i,
  // RO-Cache configuration
  input  ro_cache_ctrl_t    [NumGroups/2-1:0]                                                                   ro_cache_ctrl_i,
  // DMA request
  input  dma_req_t          [NumGroups/2-1:0]                                                                   dma_req_i,
  input  logic              [NumGroups/2-1:0]                                                                   dma_req_valid_i,
  output logic              [NumGroups/2-1:0]                                                                   dma_req_ready_o,
  // DMA status
  output dma_meta_t         [NumGroups/2-1:0]                                                                   dma_meta_o,
  // AXI Interface
  output axi_tile_req_t     [NumAXIMasters/2-1:0]                                                               axi_mst_req_o,
  input  axi_tile_resp_t    [NumAXIMasters/2-1:0]                                                               axi_mst_resp_i
);

  /************
   *  Groups  *
   ************/

  // TCDM interfaces
  tcdm_slave_req_t   [NumGroups/2-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_master_req;
  logic              [NumGroups/2-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_master_req_valid;
  logic              [NumGroups/2-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_master_req_ready;
  tcdm_master_resp_t [NumGroups/2-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_master_resp;
  logic              [NumGroups/2-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_master_resp_valid;
  logic              [NumGroups/2-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_master_resp_ready;
  tcdm_slave_req_t   [NumGroups/2-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_slave_req;
  logic              [NumGroups/2-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_slave_req_valid;
  logic              [NumGroups/2-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_slave_req_ready;
  tcdm_master_resp_t [NumGroups/2-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_slave_resp;
  logic              [NumGroups/2-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_slave_resp_valid;
  logic              [NumGroups/2-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_slave_resp_ready;

  tcdm_slave_req_t   [NumGroups/2-1:0][NumGroups-1:0][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_master_req_u;
  logic              [NumGroups/2-1:0][NumGroups-1:0][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_master_req_valid_u;
  logic              [NumGroups/2-1:0][NumGroups-1:0][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_master_req_ready_u;
  tcdm_master_resp_t [NumGroups/2-1:0][NumGroups-1:0][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_slave_resp_u;
  logic              [NumGroups/2-1:0][NumGroups-1:0][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_slave_resp_valid_u;
  logic              [NumGroups/2-1:0][NumGroups-1:0][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_slave_resp_ready_u;

  for (genvar g = 0; unsigned'(g) < NumGroups/2; g++) begin: gen_groups
    int group_id = g + NumGroups/2;
    mempool_group #(
      .TCDMBaseAddr (TCDMBaseAddr         ),
      .BootAddr     (BootAddr             )
    ) i_group (
      .clk_i                   (clk_i                                                           ),
      .rst_ni                  (rst_ni                                                          ),
      .testmode_i              (testmode_i                                                      ),
      .scan_enable_i           (scan_enable_i                                                   ),
      .scan_data_i             (/* Unconnected */                                               ),
      .scan_data_o             (/* Unconnected */                                               ),
      .group_id_i              (group_id[idx_width(NumGroups)-1:0]                              ),
      // TCDM Master interfaces
      .tcdm_master_req_o       (tcdm_master_req[g]                                              ),
      .tcdm_master_req_valid_o (tcdm_master_req_valid[g]                                        ),
      .tcdm_master_req_ready_i (tcdm_master_req_ready[g]                                        ),
      .tcdm_master_resp_i      (tcdm_master_resp[g]                                             ),
      .tcdm_master_resp_valid_i(tcdm_master_resp_valid[g]                                       ),
      .tcdm_master_resp_ready_o(tcdm_master_resp_ready[g]                                       ),
      // TCDM banks interface
      .tcdm_slave_req_i        (tcdm_slave_req[g]                                               ),
      .tcdm_slave_req_valid_i  (tcdm_slave_req_valid[g]                                         ),
      .tcdm_slave_req_ready_o  (tcdm_slave_req_ready[g]                                         ),
      .tcdm_slave_resp_o       (tcdm_slave_resp[g]                                              ),
      .tcdm_slave_resp_valid_o (tcdm_slave_resp_valid[g]                                        ),
      .tcdm_slave_resp_ready_i (tcdm_slave_resp_ready[g]                                        ),
      .wake_up_i               (wake_up_i[g*NumCoresPerGroup +: NumCoresPerGroup]               ),
      .ro_cache_ctrl_i         (ro_cache_ctrl_i[g]                                              ),
      // DMA request
      .dma_req_i               (dma_req_i[g]                                                    ),
      .dma_req_valid_i         (dma_req_valid_i[g]                                              ),
      .dma_req_ready_o         (dma_req_ready_o[g]                                              ),
      // DMA status
      .dma_meta_o              (dma_meta_o[g]                                                   ),
      // AXI interface
      .axi_mst_req_o           (axi_mst_req_o[g*NumAXIMastersPerGroup +: NumAXIMastersPerGroup] ),
      .axi_mst_resp_i          (axi_mst_resp_i[g*NumAXIMastersPerGroup +: NumAXIMastersPerGroup])
    );
  end : gen_groups

  /*******************
   *  Interconnects  *
   *******************/

  for (genvar g = 0; g < NumGroups/2; g++) begin
    for (genvar tgt = 0; tgt < NumGroups; tgt++) begin
      localparam ini = g + NumGroups/2;
      if (ini != tgt) begin
        assign tcdm_master_req_u[g][tgt]           = tcdm_master_req[g][ini ^ tgt];
        assign tcdm_master_req_valid_u[g][tgt]     = tcdm_master_req_valid[g][ini ^ tgt];
        assign tcdm_master_req_ready[g][ini ^ tgt] = tcdm_master_req_ready_u[g][tgt];
        assign tcdm_slave_resp_u[g][tgt]           = tcdm_slave_resp[g][ini ^ tgt];
        assign tcdm_slave_resp_valid_u[g][tgt]     = tcdm_slave_resp_valid[g][ini ^ tgt];
        assign tcdm_slave_resp_ready[g][ini ^ tgt] = tcdm_slave_resp_ready_u[g][tgt];
      end
    end
  end

  for (genvar g = 0; g < NumGroups/2; g++) begin
    for (genvar h = 0; h < NumGroups/2; h++) begin
      localparam ini = g + NumGroups / 2;
      localparam tgt = h + NumGroups / 2;

      // slave_req (group 2/3)   <-- master_request (group 2/3)
      // master_resp (group 2/3) <-- slave_resp (group 2/3)
      if (ini != tgt) begin
        assign tcdm_slave_req[h][ini ^ tgt]         = tcdm_master_req_u[g][tgt];
        assign tcdm_slave_req_valid[h][ini ^ tgt]   = tcdm_master_req_valid_u[g][tgt];
        assign tcdm_master_req_ready_u[g][tgt]      = tcdm_slave_req_ready[h][ini ^ tgt];
        assign tcdm_master_resp[h][ini ^ tgt]       = tcdm_slave_resp_u[g][tgt];
        assign tcdm_master_resp_valid[h][ini ^ tgt] = tcdm_slave_resp_valid_u[g][tgt];
        assign tcdm_slave_resp_ready_u[g][tgt]      = tcdm_master_resp_ready[h][ini ^ tgt];
      end

      // slave_req (group 2/3)   <-- master_request (group 0/1)
      // master_resp (group 2/3) <-- slave_resp (group 0/1)
      assign tcdm_slave_req[h][g ^ tgt]         = tcdm_master_req_i[g][tgt];
      assign tcdm_slave_req_valid[h][g ^ tgt]   = tcdm_master_req_valid_i[g][tgt];
      assign tcdm_master_req_ready_o[g][tgt]    = tcdm_slave_req_ready[h][g ^ tgt];
      assign tcdm_master_resp[h][g ^ tgt]       = tcdm_slave_resp_i[g][tgt];
      assign tcdm_master_resp_valid[h][g ^ tgt] = tcdm_slave_resp_valid_i[g][tgt];
      assign tcdm_slave_resp_ready_o[g][tgt]    = tcdm_master_resp_ready[h][g ^ tgt];

      // slave_req (group 0/1) <-- master_request (group 2/3)
      // master_resp (group 0/1) <-- slave_resp (group 2/3)
      assign tcdm_master_req_o[g][h]       = tcdm_master_req_u[g][h];
      assign tcdm_master_req_valid_o[g][h] = tcdm_master_req_valid_u[g][h];
      assign tcdm_master_req_ready_u[g][h] = tcdm_master_req_ready_i[g][h];
      assign tcdm_slave_resp_o[g][h]       = tcdm_slave_resp_u[g][h];
      assign tcdm_slave_resp_valid_o[g][h] = tcdm_slave_resp_valid_u[g][h];
      assign tcdm_slave_resp_ready_u[g][h] = tcdm_slave_resp_ready_i[g][h];
    end
  end

  /****************
   *  Assertions  *
   ****************/

  if (NumCores > 1024)
    $fatal(1, "[mempool] MemPool is currently limited to 1024 cores.");

  if (NumTiles < NumGroups)
    $fatal(1, "[mempool] MemPool requires more tiles than groups.");

  if (NumCores != NumTiles * NumCoresPerTile)
    $fatal(1, "[mempool] The number of cores is not divisible by the number of cores per tile.");

  if (BankingFactor < 1)
    $fatal(1, "[mempool] The banking factor must be a positive integer.");

  if (BankingFactor != 2**$clog2(BankingFactor))
    $fatal(1, "[mempool] The banking factor must be a power of two.");

endmodule : terapool_upper_die
