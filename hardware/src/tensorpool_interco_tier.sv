// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Interconnect tier of the TensorPool 3D stack.
//
// This is the die that faces the package substrate, so it owns the entire 2D
// boundary of the system: the AXI ports towards L2, the DMA interface, the
// wake-up and read-only-cache configuration, clock, reset and test. It carries
// no compute and very little state, which is the point: the hot Groups sit on
// the other die, with nothing between them and the heat sink.
//
// It holds
//   - the inter-Group TCDM network, NumGroups*(NumGroups-1) crossbars,
//   - the cluster DMA front end and its distribution mid-ends,
//   - the AXI cuts of the Group master ports,
//   - the wake-up and RO-cache configuration registers,
// and it propagates clock, reset and test down to every Group through the
// vertical interface.
//
// Every signal that leaves this module towards the compute tier is a hybrid
// bonding terminal, indexed by Group so that bump planning can be scripted.

`include "common_cells/registers.svh"
`include "mempool/mempool.svh"

module tensorpool_interco_tier
  import mempool_pkg::*;
  import cf_math_pkg::idx_width;
#(
  // TCDM
  parameter addr_t                 TCDMBaseAddr  = 32'b0,
  // Dependant parameter. DO NOT CHANGE!
  parameter int    unsigned        NumAXIMasters = NumGroups * NumAXIMastersPerGroup
) (
  // 2D boundary: the only package-facing interface of the whole stack
  input  logic                               clk_i,
  input  logic                               rst_ni,
  input  logic                               testmode_i,
  input  logic                               scan_enable_i,
  input  logic                               scan_data_i,
  output logic                               scan_data_o,
  input  logic           [NumCores-1:0]      wake_up_i,
  input  ro_cache_ctrl_t                     ro_cache_ctrl_i,
  input  dma_req_t                           dma_req_i,
  input  logic                               dma_req_valid_i,
  output logic                               dma_req_ready_o,
  output dma_meta_t                          dma_meta_o,
  output axi_tile_req_t  [NumAXIMasters-1:0] axi_mst_req_o,
  input  axi_tile_resp_t [NumAXIMasters-1:0] axi_mst_resp_i,
  // Vertical: clock, reset and test propagated to each Group
  output logic                               compute_clk_o,
  output logic                               compute_rst_no,
  output logic                               compute_testmode_o,
  output logic                               compute_scan_enable_o,
  // Vertical: control
  output logic           [NumCores-1:0]      compute_wake_up_o,
  output ro_cache_ctrl_t [NumGroups-1:0]     compute_ro_cache_ctrl_o,
  // Vertical: DMA
  output dma_req_t       [NumGroups-1:0]     compute_dma_req_o,
  output logic           [NumGroups-1:0]     compute_dma_req_valid_o,
  input  logic           [NumGroups-1:0]     compute_dma_req_ready_i,
  input  dma_meta_t      [NumGroups-1:0]     compute_dma_meta_i,
  // Vertical: AXI from the Groups
  input  axi_tile_req_t  [NumAXIMasters-1:0] compute_axi_mst_req_i,
  output axi_tile_resp_t [NumAXIMasters-1:0] compute_axi_mst_resp_o,
`ifdef TERAPOOL
  // Vertical: requests and responses arriving from the Groups
  input  `STRUCT_VECT(tcdm_master_req_t,  [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0]) tcdm_master_req_i,
  input  logic                            [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0]  tcdm_master_req_valid_i,
  output logic                            [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0]  tcdm_master_req_ready_o,
  input  `STRUCT_VECT(tcdm_slave_resp_t,  [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0]) tcdm_slave_resp_i,
  input  logic                            [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0]  tcdm_slave_resp_valid_i,
  output logic                            [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0]  tcdm_slave_resp_ready_o,
  // Vertical: requests and responses going back to the Groups
  output `STRUCT_VECT(tcdm_slave_req_t,   [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0]) tcdm_slave_req_o,
  output logic                            [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0]  tcdm_slave_req_valid_o,
  input  logic                            [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0]  tcdm_slave_req_ready_i,
  output `STRUCT_VECT(tcdm_master_resp_t, [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0]) tcdm_master_resp_o,
  output logic                            [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0]  tcdm_master_resp_valid_o,
  input  logic                            [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0]  tcdm_master_resp_ready_i
`else
  // Vertical: requests and responses arriving from the Groups
  input  `STRUCT_VECT(tcdm_slave_req_t,   [NumGroups-1:0][NumGroups-1:1][NumTilesPerGroup-1:0]) tcdm_master_req_i,
  input  logic                            [NumGroups-1:0][NumGroups-1:1][NumTilesPerGroup-1:0]  tcdm_master_req_valid_i,
  output logic                            [NumGroups-1:0][NumGroups-1:1][NumTilesPerGroup-1:0]  tcdm_master_req_ready_o,
  input  `STRUCT_VECT(tcdm_master_resp_t, [NumGroups-1:0][NumGroups-1:1][NumTilesPerGroup-1:0]) tcdm_slave_resp_i,
  input  logic                            [NumGroups-1:0][NumGroups-1:1][NumTilesPerGroup-1:0]  tcdm_slave_resp_valid_i,
  output logic                            [NumGroups-1:0][NumGroups-1:1][NumTilesPerGroup-1:0]  tcdm_slave_resp_ready_o,
  // Vertical: requests and responses going back to the Groups
  output `STRUCT_VECT(tcdm_slave_req_t,   [NumGroups-1:0][NumGroups-1:1][NumTilesPerGroup-1:0]) tcdm_slave_req_o,
  output logic                            [NumGroups-1:0][NumGroups-1:1][NumTilesPerGroup-1:0]  tcdm_slave_req_valid_o,
  input  logic                            [NumGroups-1:0][NumGroups-1:1][NumTilesPerGroup-1:0]  tcdm_slave_req_ready_i,
  output `STRUCT_VECT(tcdm_master_resp_t, [NumGroups-1:0][NumGroups-1:1][NumTilesPerGroup-1:0]) tcdm_master_resp_o,
  output logic                            [NumGroups-1:0][NumGroups-1:1][NumTilesPerGroup-1:0]  tcdm_master_resp_valid_o,
  input  logic                            [NumGroups-1:0][NumGroups-1:1][NumTilesPerGroup-1:0]  tcdm_master_resp_ready_i
`endif
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
  dma_req_t  [NumGroups-1:0] dma_req_group, dma_req_group_q;
  logic      [NumGroups-1:0] dma_req_group_valid, dma_req_group_q_valid;
  logic      [NumGroups-1:0] dma_req_group_ready, dma_req_group_q_ready;
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
    .burst_req_o (dma_req_group      ),
    .valid_o     (dma_req_group_valid),
    .ready_i     (dma_req_group_ready),
    .meta_i      (dma_meta_q         )
  );

  for (genvar g = 0; unsigned'(g) < NumGroups; g++) begin: gen_dma_req_group_register
    spill_register #(
      .T(dma_req_t)
    ) i_dma_req_group_register (
      .clk_i  (clk_i                   ),
      .rst_ni (rst_ni                  ),
      .data_i (dma_req_group[g]        ),
      .valid_i(dma_req_group_valid[g]  ),
      .ready_o(dma_req_group_ready[g]  ),
      .data_o (dma_req_group_q[g]      ),
      .valid_o(dma_req_group_q_valid[g]),
      .ready_i(dma_req_group_q_ready[g])
    );
  end : gen_dma_req_group_register

  /********************************
   *  Propagation to compute tier *
   ********************************/
  // Clock, reset and test are driven down as single nets. How many bond
  // terminals carry them, and where they sit over the compute die, is a
  // floorplan decision and does not belong in the RTL.
  assign compute_clk_o           = clk_i;
  assign compute_rst_no          = rst_ni;
  assign compute_testmode_o      = testmode_i;
  assign compute_scan_enable_o   = scan_enable_i;
  assign compute_wake_up_o       = wake_up_q;
  assign compute_ro_cache_ctrl_o = ro_cache_ctrl_q;
  assign compute_dma_req_o       = dma_req_group_q;
  assign compute_dma_req_valid_o = dma_req_group_q_valid;
  assign dma_req_group_q_ready   = compute_dma_req_ready_i;
  assign dma_meta                = compute_dma_meta_i;

  `ifdef TERAPOOL
      /************
       *  Groups  *
       ************/
      // TCDM interfaces
      tcdm_master_req_t  [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_master_req;
      logic              [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_master_req_valid;
      logic              [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_master_req_ready;
      tcdm_master_resp_t [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_master_resp;
      logic              [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_master_resp_valid;
      logic              [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_master_resp_ready;
      tcdm_slave_req_t   [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_slave_req;
      logic              [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_slave_req_valid;
      logic              [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_slave_req_ready;
      tcdm_slave_resp_t  [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_slave_resp;
      logic              [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_slave_resp_valid;
      logic              [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0] tcdm_slave_resp_ready;

      /**********************
       *    AXI Register    *
       **********************/
      // Additional AXI registers for breaking TeraPool's long paths
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

    assign axi_mst_req            = compute_axi_mst_req_i;
    assign compute_axi_mst_resp_o = axi_mst_resp;

    // The vertical ports feed the inter-Group network.
    assign tcdm_master_req          = tcdm_master_req_i;
    assign tcdm_master_req_valid    = tcdm_master_req_valid_i;
    assign tcdm_master_req_ready_o  = tcdm_master_req_ready;
    assign tcdm_slave_resp          = tcdm_slave_resp_i;
    assign tcdm_slave_resp_valid    = tcdm_slave_resp_valid_i;
    assign tcdm_slave_resp_ready_o  = tcdm_slave_resp_ready;
    assign tcdm_slave_req_o         = tcdm_slave_req;
    assign tcdm_slave_req_valid_o   = tcdm_slave_req_valid;
    assign tcdm_slave_req_ready     = tcdm_slave_req_ready_i;
    assign tcdm_master_resp_o       = tcdm_master_resp;
    assign tcdm_master_resp_valid_o = tcdm_master_resp_valid;
    assign tcdm_master_resp_ready   = tcdm_master_resp_ready_i;


      /*******************
       *  Interconnects  *
       *******************/
      // The inter-Group network. One crossbar per directed Group-to-Group link:
      // Group `ini` reaches Group `ini ^ r` through its remote port `r`, which is
      // what the XOR addressing of the TCDM address map expects. The local
      // connections stay inside the Groups.
      //
      // This is the level that the 3D flow relocates to the top tier: every port
      // of every instance below is registered on the Group side, so cutting here
      // costs no pipeline stage.

      for (genvar ini = 0; ini < NumGroups; ini++) begin: gen_inter_group_interco_ini
        for (genvar r = 1; r < NumGroups; r++) begin: gen_inter_group_interco_r
          tensorpool_inter_group_interco i_inter_group_interco (
            .clk_i                   (clk_i                              ),
            .rst_ni                  (rst_ni                             ),
            // Initiator side, towards Group `ini`
            .tcdm_master_req_i       (tcdm_master_req[ini][r]            ),
            .tcdm_master_req_valid_i (tcdm_master_req_valid[ini][r]      ),
            .tcdm_master_req_ready_o (tcdm_master_req_ready[ini][r]      ),
            .tcdm_slave_resp_i       (tcdm_slave_resp[ini][r]            ),
            .tcdm_slave_resp_valid_i (tcdm_slave_resp_valid[ini][r]      ),
            .tcdm_slave_resp_ready_o (tcdm_slave_resp_ready[ini][r]      ),
            // Target side, towards Group `ini ^ r`
            .tcdm_slave_req_o        (tcdm_slave_req[ini ^ r][r]         ),
            .tcdm_slave_req_valid_o  (tcdm_slave_req_valid[ini ^ r][r]   ),
            .tcdm_slave_req_ready_i  (tcdm_slave_req_ready[ini ^ r][r]   ),
            .tcdm_master_resp_o      (tcdm_master_resp[ini ^ r][r]       ),
            .tcdm_master_resp_valid_o(tcdm_master_resp_valid[ini ^ r][r] ),
            .tcdm_master_resp_ready_i(tcdm_master_resp_ready[ini ^ r][r] )
          );
        end: gen_inter_group_interco_r
      end: gen_inter_group_interco_ini

  `else
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

    // MemPool and MinPool have no AXI cut at cluster level.
    assign axi_mst_req_o          = compute_axi_mst_req_i;
    assign compute_axi_mst_resp_o = axi_mst_resp_i;

    // The vertical ports feed the inter-Group network.
    assign tcdm_master_req          = tcdm_master_req_i;
    assign tcdm_master_req_valid    = tcdm_master_req_valid_i;
    assign tcdm_master_req_ready_o  = tcdm_master_req_ready;
    assign tcdm_slave_resp          = tcdm_slave_resp_i;
    assign tcdm_slave_resp_valid    = tcdm_slave_resp_valid_i;
    assign tcdm_slave_resp_ready_o  = tcdm_slave_resp_ready;
    assign tcdm_slave_req_o         = tcdm_slave_req;
    assign tcdm_slave_req_valid_o   = tcdm_slave_req_valid;
    assign tcdm_slave_req_ready     = tcdm_slave_req_ready_i;
    assign tcdm_master_resp_o       = tcdm_master_resp;
    assign tcdm_master_resp_valid_o = tcdm_master_resp_valid;
    assign tcdm_master_resp_ready   = tcdm_master_resp_ready_i;


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
  `endif

endmodule : tensorpool_interco_tier
