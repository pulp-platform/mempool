// Copyright 2021 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "common_cells/registers.svh"

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

  /*********************
   *  Control Signals  *
   *********************/
  logic [NumCores-1:0] wake_up_q;
  `FF(wake_up_q, wake_up_i, '0, clk_i, rst_ni);

  ro_cache_ctrl_t [NumGroups-1:0] ro_cache_ctrl_q;
  for (genvar g = 0; unsigned'(g) < NumGroups; g++) begin: gen_ro_cache_ctrl_q
    `FF(ro_cache_ctrl_q[g], ro_cache_ctrl_i, ro_cache_ctrl_default, clk_i, rst_ni);
  end: gen_ro_cache_ctrl_q

  /**********************
   *    AXI Register    *
   **********************/
  // AXI interfaces
  axi_tile_req_t   [NumAXIMasters-1:0] axi_mst_req;
  axi_tile_resp_t  [NumAXIMasters-1:0] axi_mst_resp;

  for (genvar m = 0; m < NumAXIMasters; m++) begin: gen_axi_group_cuts
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

  /*********
   *  DMA  *
   *********/
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

  dma_req_t  dma_req_split;
  logic      dma_req_split_valid;
  logic      dma_req_split_ready;
  dma_meta_t dma_meta_split;
  dma_req_t  [NumGroups-1:0] dma_req;
  logic      [NumGroups-1:0] dma_req_valid;
  logic      [NumGroups-1:0] dma_req_ready;
  dma_meta_t [NumGroups-1:0] dma_meta, dma_meta_q;

  `FF(dma_meta_q, dma_meta, '0, clk_i, rst_ni);

  idma_split_midend #(
    .DmaRegionWidth (NumBanksPerGroup*NumGroups*4),
    .DmaRegionStart (TCDMBaseAddr                ),
    .DmaRegionEnd   (TCDMBaseAddr+TCDMSize       ),
    .AddrWidth      (AddrWidth                   ),
    .burst_req_t    (dma_req_t                   ),
    .meta_t         (dma_meta_t                  )
  ) i_idma_split_midend (
    .clk_i      (clk_i              ),
    .rst_ni     (rst_ni             ),
    .burst_req_i(dma_req_cut        ),
    .valid_i    (dma_req_cut_valid  ),
    .ready_o    (dma_req_cut_ready  ),
    .meta_o     (dma_meta_cut       ),
    .burst_req_o(dma_req_split      ),
    .valid_o    (dma_req_split_valid),
    .ready_i    (dma_req_split_ready),
    .meta_i     (dma_meta_split     )
  );

  idma_distributed_midend #(
    .NoMstPorts     (NumGroups            ),
    .DmaRegionWidth (NumBanksPerGroup*4   ),
    .DmaRegionStart (TCDMBaseAddr         ),
    .DmaRegionEnd   (TCDMBaseAddr+TCDMSize),
    .TransFifoDepth (16                   ),
    .burst_req_t    (dma_req_t            ),
    .meta_t         (dma_meta_t           )
  ) i_idma_distributed_midend (
    .clk_i       (clk_i              ),
    .rst_ni      (rst_ni             ),
    .burst_req_i (dma_req_split      ),
    .valid_i     (dma_req_split_valid),
    .ready_o     (dma_req_split_ready),
    .meta_o      (dma_meta_split     ),
    .burst_req_o (dma_req            ),
    .valid_o     (dma_req_valid      ),
    .ready_i     (dma_req_ready      ),
    .meta_i      (dma_meta_q         )
  );

  /************
   *  Groups  *
   ************/
  // TCDM interfaces
  tcdm_slave_req_t   [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_master_req;
  logic              [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_master_req_valid;
  logic              [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_master_req_ready;
  tcdm_master_resp_t [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_master_resp;
  logic              [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_master_resp_valid;
  logic              [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_master_resp_ready;
  tcdm_slave_req_t   [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_slave_req;
  logic              [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_slave_req_valid;
  logic              [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_slave_req_ready;
  tcdm_master_resp_t [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_slave_resp;
  logic              [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_slave_resp_valid;
  logic              [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_slave_resp_ready;
  
  tcdm_slave_req_t   [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_master_req_postreg;
  logic              [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_master_req_valid_postreg;
  logic              [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_master_req_ready_postreg;
  tcdm_master_resp_t [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_master_resp_postreg;
  logic              [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_master_resp_valid_postreg;
  logic              [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_master_resp_ready_postreg;
  tcdm_slave_req_t   [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_slave_req_postreg;
  logic              [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_slave_req_valid_postreg;
  logic              [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_slave_req_ready_postreg;
  tcdm_master_resp_t [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_slave_resp_postreg;
  logic              [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_slave_resp_valid_postreg;
  logic              [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_slave_resp_ready_postreg;

  /***************
   *  Registers  *
   ***************/
  // Break paths between request and response with registers
  for (genvar g = 0; unsigned'(g) < NumGroups; g++) begin: gen_tcdm_registers_g
    for (genvar h = 1; unsigned'(h) < NumGroups; h++) begin: gen_tcdm_registers_h
      for (genvar sg = 0; unsigned'(sg) < NumSubGroupsPerGroup; sg++) begin: gen_tcdm_registers_sg
        for (genvar t = 0; unsigned'(t) < NumTilesPerSubGroup; t++) begin: gen_tcdm_registers_t
          //TCDM  
          spill_register #(
            .T(tcdm_master_req_t)
          ) i_tcdm_master_req_register (
            .clk_i  (clk_i                                         ),
            .rst_ni (rst_ni                                        ),
            .data_i (tcdm_master_req[g][h][sg][t]                  ),
            .valid_i(tcdm_master_req_valid[g][h][sg][t]            ),
            .ready_o(tcdm_master_req_ready[g][h][sg][t]            ),
            .data_o (tcdm_master_req_postreg[g][h][sg][t]          ),
            .valid_o(tcdm_master_req_valid_postreg[g][h][sg][t]    ),
            .ready_i(tcdm_master_req_ready_postreg[g][h][sg][t]    )
          );
    
          fall_through_register #(
            .T(tcdm_master_resp_t)
          ) i_tcdm_master_resp_register (
            .clk_i     (clk_i                                      ),
            .rst_ni    (rst_ni                                     ),
            .clr_i     (1'b0                                       ),
            .testmode_i(1'b0                                       ),
            .data_i    (tcdm_master_resp_postreg[g][h][sg][t]      ),
            .valid_i   (tcdm_master_resp_valid_postreg[g][h][sg][t]),
            .ready_o   (tcdm_master_resp_ready_postreg[g][h][sg][t]),
            .data_o    (tcdm_master_resp[g][h][sg][t]              ),
            .valid_o   (tcdm_master_resp_valid[g][h][sg][t]        ),
            .ready_i   (tcdm_master_resp_ready[g][h][sg][t]        )
          );
    
          fall_through_register #(
            .T(tcdm_slave_req_t)
          ) i_tcdm_slave_req_register (
            .clk_i     (clk_i                                      ),
            .rst_ni    (rst_ni                                     ),
            .clr_i     (1'b0                                       ),
            .testmode_i(1'b0                                       ),
            .data_i    (tcdm_slave_req_postreg[g][h][sg][t]        ),
            .valid_i   (tcdm_slave_req_valid_postreg[g][h][sg][t]  ),
            .ready_o   (tcdm_slave_req_ready_postreg[g][h][sg][t]  ),
            .data_o    (tcdm_slave_req[g][h][sg][t]                ),
            .valid_o   (tcdm_slave_req_valid[g][h][sg][t]          ),
            .ready_i   (tcdm_slave_req_ready[g][h][sg][t]          )
          );
    
          spill_register #(
            .T(tcdm_slave_resp_t)
          ) i_tcdm_slave_resp_register (
            .clk_i  (clk_i                                         ),
            .rst_ni (rst_ni                                        ),
            .data_i (tcdm_slave_resp[g][h][sg][t]                  ),
            .valid_i(tcdm_slave_resp_valid[g][h][sg][t]            ),
            .ready_o(tcdm_slave_resp_ready[g][h][sg][t]            ),
            .data_o (tcdm_slave_resp_postreg[g][h][sg][t]          ),
            .valid_o(tcdm_slave_resp_valid_postreg[g][h][sg][t]    ),
            .ready_i(tcdm_slave_resp_ready_postreg[g][h][sg][t]    )
          );
        end: gen_tcdm_registers_t
      end: gen_tcdm_registers_sg
    end: gen_tcdm_registers_h
  end: gen_tcdm_registers_g

`ifdef POSTLAYOUT
  for (genvar g = 0; unsigned'(g) < NumGroups; g++) begin: gen_groups
    mempool_group i_group (
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
      .wake_up_i               (wake_up_q[g*NumCoresPerGroup +: NumCoresPerGroup]               ),
      .ro_cache_ctrl_i         (ro_cache_ctrl_q[g]                                              ),
      // DMA request
      .dma_req_i               (dma_req[g]                                                      ),
      .dma_req_valid_i         (dma_req_valid[g]                                                ),
      .dma_req_ready_o         (dma_req_ready[g]                                                ),
      // DMA status
      .dma_meta_o_backend_idle_   (dma_meta[g][0]                                               ),
      .dma_meta_o_trans_complete_ (dma_meta[g][1]                                               ),
      //.dma_meta_o              (dma_meta[g]                                                     ),
      // AXI interface
      .axi_mst_req_o           (axi_mst_req[g*NumAXIMastersPerGroup +: NumAXIMastersPerGroup] ),
      .axi_mst_resp_i          (axi_mst_resp[g*NumAXIMastersPerGroup +: NumAXIMastersPerGroup])
    );
  end : gen_groups
`else
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
      .wake_up_i               (wake_up_q[g*NumCoresPerGroup +: NumCoresPerGroup]               ),
      .ro_cache_ctrl_i         (ro_cache_ctrl_q[g]                                              ),
      // DMA request
      .dma_req_i               (dma_req[g]                                                      ),
      .dma_req_valid_i         (dma_req_valid[g]                                                ),
      .dma_req_ready_o         (dma_req_ready[g]                                                ),
      // DMA status
      .dma_meta_o              (dma_meta[g]                                                     ),
      // AXI interface
      .axi_mst_req_o           (axi_mst_req[g*NumAXIMastersPerGroup +: NumAXIMastersPerGroup] ),
      .axi_mst_resp_i          (axi_mst_resp[g*NumAXIMastersPerGroup +: NumAXIMastersPerGroup])
    );
  end : gen_groups
`endif

  /*******************
   *  Interconnects  *
   *******************/

  for (genvar ini = 0; ini < NumGroups; ini++) begin: gen_interconnections_ini
    for (genvar tgt = 0; tgt < NumGroups; tgt++) begin: gen_interconnections_tgt
      // The local connections are inside the groups
      if (ini != tgt) begin: gen_remote_interconnections
        assign tcdm_slave_req_postreg[tgt][ini ^ tgt]        = tcdm_master_req_postreg[ini][ini ^ tgt];
        assign tcdm_slave_req_valid_postreg[tgt][ini ^ tgt]  = tcdm_master_req_valid_postreg[ini][ini ^ tgt];
        assign tcdm_master_req_ready_postreg[ini][ini ^ tgt] = tcdm_slave_req_ready_postreg[tgt][ini ^ tgt];

        assign tcdm_master_resp_postreg[tgt][ini ^ tgt]       = tcdm_slave_resp_postreg[ini][ini ^ tgt];
        assign tcdm_master_resp_valid_postreg[tgt][ini ^ tgt] = tcdm_slave_resp_valid_postreg[ini][ini ^ tgt];
        assign tcdm_slave_resp_ready_postreg[ini][ini ^ tgt]  = tcdm_master_resp_ready_postreg[tgt][ini ^ tgt];
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
