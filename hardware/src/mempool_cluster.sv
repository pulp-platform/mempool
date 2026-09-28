// Copyright 2021 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Assembly of the two TensorPool tiers.
//
// This module is the 3D top level: it instantiates one interconnect tier and
// one compute tier and does nothing else. Every net declared here is a
// die-to-die connection, and the external boundary of the cluster is the
// boundary of the interconnect tier alone, because the compute tier has no
// package-facing I/O.
//
//   substrate / PCB
//        |  C4
//   tensorpool_interco_tier    inter-Group network, DMA, AXI, control
//        |  hybrid bonding terminals
//   tensorpool_compute_tier    NumGroups x mempool_group
//        |
//   heat sink
//
// Keeping the port list of mempool_cluster unchanged means mempool_system and
// the testbench do not have to know that the cluster is stacked.

`include "mempool/mempool.svh"

module mempool_cluster
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
  input  logic                               clk_i,
  input  logic                               rst_ni,
  input  logic                               testmode_i,
  // Scan chain
  input  logic                               scan_enable_i,
  input  logic                               scan_data_i,
  output logic                               scan_data_o,
  // Wake up signal
  input  logic           [NumCores-1:0]      wake_up_i,
  // RO-Cache configuration
  input  ro_cache_ctrl_t                     ro_cache_ctrl_i,
  // DMA request
  input  dma_req_t                           dma_req_i,
  input  logic                               dma_req_valid_i,
  output logic                               dma_req_ready_o,
  // DMA status
  output dma_meta_t                          dma_meta_o,
  // AXI Interface
  output axi_tile_req_t  [NumAXIMasters-1:0] axi_mst_req_o,
  input  axi_tile_resp_t [NumAXIMasters-1:0] axi_mst_resp_i
);

  /**************************
   *  Die-to-die interface  *
   **************************/
  // Control, clock and reset travel downwards; TCDM traffic travels both ways.
  logic                               d2d_clk;
  logic                               d2d_rst_n;
  logic                               d2d_testmode;
  logic                               d2d_scan_enable;
  logic           [NumCores-1:0]      d2d_wake_up;
  ro_cache_ctrl_t [NumGroups-1:0]     d2d_ro_cache_ctrl;
  dma_req_t       [NumGroups-1:0]     d2d_dma_req;
  logic           [NumGroups-1:0]     d2d_dma_req_valid;
  logic           [NumGroups-1:0]     d2d_dma_req_ready;
  dma_meta_t      [NumGroups-1:0]     d2d_dma_meta;
  axi_tile_req_t  [NumAXIMasters-1:0] d2d_axi_mst_req;
  axi_tile_resp_t [NumAXIMasters-1:0] d2d_axi_mst_resp;

  `ifdef TERAPOOL
    tcdm_master_req_t  [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] d2d_tcdm_master_req;
    logic              [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] d2d_tcdm_master_req_valid;
    logic              [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] d2d_tcdm_master_req_ready;
    tcdm_slave_resp_t  [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] d2d_tcdm_slave_resp;
    logic              [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] d2d_tcdm_slave_resp_valid;
    logic              [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] d2d_tcdm_slave_resp_ready;
    tcdm_slave_req_t   [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] d2d_tcdm_slave_req;
    logic              [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] d2d_tcdm_slave_req_valid;
    logic              [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] d2d_tcdm_slave_req_ready;
    tcdm_master_resp_t [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] d2d_tcdm_master_resp;
    logic              [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] d2d_tcdm_master_resp_valid;
    logic              [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] d2d_tcdm_master_resp_ready;
  `else
    tcdm_slave_req_t   [NumGroups-1:0][NumGroups-1:1][NumTilesPerGroup-1:0] d2d_tcdm_master_req;
    logic              [NumGroups-1:0][NumGroups-1:1][NumTilesPerGroup-1:0] d2d_tcdm_master_req_valid;
    logic              [NumGroups-1:0][NumGroups-1:1][NumTilesPerGroup-1:0] d2d_tcdm_master_req_ready;
    tcdm_master_resp_t [NumGroups-1:0][NumGroups-1:1][NumTilesPerGroup-1:0] d2d_tcdm_slave_resp;
    logic              [NumGroups-1:0][NumGroups-1:1][NumTilesPerGroup-1:0] d2d_tcdm_slave_resp_valid;
    logic              [NumGroups-1:0][NumGroups-1:1][NumTilesPerGroup-1:0] d2d_tcdm_slave_resp_ready;
    tcdm_slave_req_t   [NumGroups-1:0][NumGroups-1:1][NumTilesPerGroup-1:0] d2d_tcdm_slave_req;
    logic              [NumGroups-1:0][NumGroups-1:1][NumTilesPerGroup-1:0] d2d_tcdm_slave_req_valid;
    logic              [NumGroups-1:0][NumGroups-1:1][NumTilesPerGroup-1:0] d2d_tcdm_slave_req_ready;
    tcdm_master_resp_t [NumGroups-1:0][NumGroups-1:1][NumTilesPerGroup-1:0] d2d_tcdm_master_resp;
    logic              [NumGroups-1:0][NumGroups-1:1][NumTilesPerGroup-1:0] d2d_tcdm_master_resp_valid;
    logic              [NumGroups-1:0][NumGroups-1:1][NumTilesPerGroup-1:0] d2d_tcdm_master_resp_ready;
  `endif

  /***********************
   *  Interconnect tier  *
   ***********************/

  tensorpool_interco_tier #(
    .TCDMBaseAddr(TCDMBaseAddr)
  ) i_interco_tier (
    // 2D boundary
    .clk_i                    (clk_i                     ),
    .rst_ni                   (rst_ni                    ),
    .testmode_i               (testmode_i                ),
    .scan_enable_i            (scan_enable_i             ),
    .scan_data_i              (scan_data_i               ),
    .scan_data_o              (scan_data_o               ),
    .wake_up_i                (wake_up_i                 ),
    .ro_cache_ctrl_i          (ro_cache_ctrl_i           ),
    .dma_req_i                (dma_req_i                 ),
    .dma_req_valid_i          (dma_req_valid_i           ),
    .dma_req_ready_o          (dma_req_ready_o           ),
    .dma_meta_o               (dma_meta_o                ),
    .axi_mst_req_o            (axi_mst_req_o             ),
    .axi_mst_resp_i           (axi_mst_resp_i            ),
    // Vertical
    .compute_clk_o            (d2d_clk                   ),
    .compute_rst_no           (d2d_rst_n                 ),
    .compute_testmode_o       (d2d_testmode              ),
    .compute_scan_enable_o    (d2d_scan_enable           ),
    .compute_wake_up_o        (d2d_wake_up               ),
    .compute_ro_cache_ctrl_o  (d2d_ro_cache_ctrl         ),
    .compute_dma_req_o        (d2d_dma_req               ),
    .compute_dma_req_valid_o  (d2d_dma_req_valid         ),
    .compute_dma_req_ready_i  (d2d_dma_req_ready         ),
    .compute_dma_meta_i       (d2d_dma_meta              ),
    .compute_axi_mst_req_i    (d2d_axi_mst_req           ),
    .compute_axi_mst_resp_o   (d2d_axi_mst_resp          ),
    .tcdm_master_req_i        (d2d_tcdm_master_req       ),
    .tcdm_master_req_valid_i  (d2d_tcdm_master_req_valid ),
    .tcdm_master_req_ready_o  (d2d_tcdm_master_req_ready ),
    .tcdm_slave_resp_i        (d2d_tcdm_slave_resp       ),
    .tcdm_slave_resp_valid_i  (d2d_tcdm_slave_resp_valid ),
    .tcdm_slave_resp_ready_o  (d2d_tcdm_slave_resp_ready ),
    .tcdm_slave_req_o         (d2d_tcdm_slave_req        ),
    .tcdm_slave_req_valid_o   (d2d_tcdm_slave_req_valid  ),
    .tcdm_slave_req_ready_i   (d2d_tcdm_slave_req_ready  ),
    .tcdm_master_resp_o       (d2d_tcdm_master_resp      ),
    .tcdm_master_resp_valid_o (d2d_tcdm_master_resp_valid),
    .tcdm_master_resp_ready_i (d2d_tcdm_master_resp_ready)
  );

  /******************
   *  Compute tier  *
   ******************/

  tensorpool_compute_tier #(
    .TCDMBaseAddr(TCDMBaseAddr),
    .BootAddr    (BootAddr    )
  ) i_compute_tier (
    // Vertical only: this die has no package-facing I/O
    .clk_i                    (d2d_clk                   ),
    .rst_ni                   (d2d_rst_n                 ),
    .testmode_i               (d2d_testmode              ),
    .scan_enable_i            (d2d_scan_enable           ),
    .wake_up_i                (d2d_wake_up               ),
    .ro_cache_ctrl_i          (d2d_ro_cache_ctrl         ),
    .dma_req_i                (d2d_dma_req               ),
    .dma_req_valid_i          (d2d_dma_req_valid         ),
    .dma_req_ready_o          (d2d_dma_req_ready         ),
    .dma_meta_o               (d2d_dma_meta              ),
    .axi_mst_req_o            (d2d_axi_mst_req           ),
    .axi_mst_resp_i           (d2d_axi_mst_resp          ),
    .tcdm_master_req_o        (d2d_tcdm_master_req       ),
    .tcdm_master_req_valid_o  (d2d_tcdm_master_req_valid ),
    .tcdm_master_req_ready_i  (d2d_tcdm_master_req_ready ),
    .tcdm_slave_resp_o        (d2d_tcdm_slave_resp       ),
    .tcdm_slave_resp_valid_o  (d2d_tcdm_slave_resp_valid ),
    .tcdm_slave_resp_ready_i  (d2d_tcdm_slave_resp_ready ),
    .tcdm_slave_req_i         (d2d_tcdm_slave_req        ),
    .tcdm_slave_req_valid_i   (d2d_tcdm_slave_req_valid  ),
    .tcdm_slave_req_ready_o   (d2d_tcdm_slave_req_ready  ),
    .tcdm_master_resp_i       (d2d_tcdm_master_resp      ),
    .tcdm_master_resp_valid_i (d2d_tcdm_master_resp_valid),
    .tcdm_master_resp_ready_o (d2d_tcdm_master_resp_ready)
  );

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

endmodule : mempool_cluster
