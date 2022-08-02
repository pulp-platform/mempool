// Copyright 2021 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

module mempool_cluster
  import mempool_pkg::*;
  import cf_math_pkg::idx_width;
#(
  // TCDM
  parameter addr_t                 TCDMBaseAddr  = 32'b0,
  // Boot address
  parameter logic           [31:0] BootAddr      = 32'h0000_0000,
  // Dependant parameters. DO NOT CHANGE!
  parameter int    unsigned        NumDMAReq     = NumGroups * NumDMAsPerGroup,
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
  input  dma_req_t       [NumDMAReq-1:0]     dma_req_i,
  input  logic           [NumDMAReq-1:0]     dma_req_valid_i,
  output logic           [NumDMAReq-1:0]     dma_req_ready_o,
  // AXI Interface
  output axi_tile_req_t  [NumAXIMasters-1:0] axi_mst_req_o,
  input  axi_tile_resp_t [NumAXIMasters-1:0] axi_mst_resp_i
);

  /************
   *  Groups  *
   ************/

  // TCDM interfaces
  tcdm_slave_req_t   [NumGroups-1:0][NumGroups-1:1][NumTilesPerGroup-1:0] tcdm_master_req;
  logic              [NumGroups-1:0][NumGroups-1:1][NumTilesPerGroup-1:0] tcdm_master_req_valid;
  logic              [NumGroups-1:0][NumGroups-1:1][NumTilesPerGroup-1:0] tcdm_master_req_ready;
  tcdm_master_resp_t [NumGroups-1:0][NumGroups-1:1][NumTilesPerGroup-1:0] tcdm_master_resp;
  logic              [NumGroups-1:0][NumGroups-1:1][NumTilesPerGroup-1:0] tcdm_master_resp_valid;
  logic              [NumGroups-1:0][NumGroups-1:1][NumTilesPerGroup-1:0] tcdm_master_resp_ready;
  tcdm_slave_req_t   [NumGroups-1:0][NumGroups-1:1][NumTilesPerGroup-1:0] tcdm_slave_req;
  logic              [NumGroups-1:0][NumGroups-1:1][NumTilesPerGroup-1:0] tcdm_slave_req_valid;
  logic              [NumGroups-1:0][NumGroups-1:1][NumTilesPerGroup-1:0] tcdm_slave_req_ready;
  tcdm_master_resp_t [NumGroups-1:0][NumGroups-1:1][NumTilesPerGroup-1:0] tcdm_slave_resp;
  logic              [NumGroups-1:0][NumGroups-1:1][NumTilesPerGroup-1:0] tcdm_slave_resp_valid;
  logic              [NumGroups-1:0][NumGroups-1:1][NumTilesPerGroup-1:0] tcdm_slave_resp_ready;

  for (genvar g = 0; unsigned'(g) < NumGroups; g++) begin: gen_groups
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
      .group_id_i              (g[idx_width(NumGroups)-1:0]                                     ),
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
      .ro_cache_ctrl_i         (ro_cache_ctrl_i                                                 ),
      // DMA request
      .dma_req_i               (dma_req_i[g*NumDMAsPerGroup +: NumDMAsPerGroup]                 ),
      .dma_req_valid_i         (dma_req_valid_i[g*NumDMAsPerGroup +: NumDMAsPerGroup]           ),
      .dma_req_ready_o         (dma_req_ready_o[g*NumDMAsPerGroup +: NumDMAsPerGroup]           ),
      // AXI interface
      .axi_mst_req_o           (axi_mst_req_o[g*NumAXIMastersPerGroup +: NumAXIMastersPerGroup] ),
      .axi_mst_resp_i          (axi_mst_resp_i[g*NumAXIMastersPerGroup +: NumAXIMastersPerGroup])
    );
  end : gen_groups

  /*******************
   *  Interconnects  *
   *******************/

  for (genvar ini = 0; ini < NumGroups; ini++) begin: gen_interconnections_ini
    for (genvar tgt = 0; tgt < NumGroups; tgt++) begin: gen_interconnections_tgt
      // The local connections are inside the groups
      if (ini != tgt) begin: gen_remote_interconnections
        assign tcdm_slave_req[tgt][ini ^ tgt]        = tcdm_master_req[ini][ini ^ tgt];
        assign tcdm_slave_req_valid[tgt][ini ^ tgt]  = tcdm_master_req_valid[ini][ini ^ tgt];
        assign tcdm_master_req_ready[ini][ini ^ tgt] = tcdm_slave_req_ready[tgt][ini ^ tgt];

        assign tcdm_master_resp[tgt][ini ^ tgt]       = tcdm_slave_resp[ini][ini ^ tgt];
        assign tcdm_master_resp_valid[tgt][ini ^ tgt] = tcdm_slave_resp_valid[ini][ini ^ tgt];
        assign tcdm_slave_resp_ready[ini][ini ^ tgt]  = tcdm_master_resp_ready[tgt][ini ^ tgt];
      end: gen_remote_interconnections
    end: gen_interconnections_tgt
  end: gen_interconnections_ini

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
