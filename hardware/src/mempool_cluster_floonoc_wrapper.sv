// Copyright 2024 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "common_cells/registers.svh"

module mempool_cluster_floonoc_wrapper
  import mempool_pkg::*;
  import cf_math_pkg::idx_width;
  import floo_pkg::*;
  import floo_terapool_noc_pkg::*;
#(
  // TCDM
  parameter addr_t                 TCDMBaseAddr  = 32'b0,
  // Boot address
  parameter logic  [31:0]          BootAddr      = 32'h0000_0000,
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
  input  axi_tile_resp_t [NumAXIMasters-1:0] axi_mst_resp_i,
  // Periph Interface
  output axi_tile_req_t                      periph_mst_req_o,
  input  axi_tile_resp_t                     periph_mst_resp_i,
  // Host Interface
  input  axi_tile_req_t                      host_slv_req_i,
  output axi_tile_resp_t                     host_slv_resp_o
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

  /************
    *  Groups  *
    ************/

  // narrow req noc
  `ifdef USE_NARROW_REQ_CHANNEL
  floo_tcdm_rd_req_t    [NumX-1:0][NumY-1:0][West:North][NumTilesPerGroup-1:0][NumNarrowRemoteReqPortsPerTile-1:0] floo_tcdm_narrow_req_in;
  logic                 [NumX-1:0][NumY-1:0][West:North][NumTilesPerGroup-1:0][NumNarrowRemoteReqPortsPerTile-1:0][NumVirtualChannel-1:0] floo_tcdm_narrow_req_in_ready, floo_tcdm_narrow_req_in_valid;
  floo_tcdm_rd_req_t    [NumX-1:0][NumY-1:0][West:North][NumTilesPerGroup-1:0][NumNarrowRemoteReqPortsPerTile-1:0] floo_tcdm_narrow_req_out;
  logic                 [NumX-1:0][NumY-1:0][West:North][NumTilesPerGroup-1:0][NumNarrowRemoteReqPortsPerTile-1:0][NumVirtualChannel-1:0] floo_tcdm_narrow_req_out_ready, floo_tcdm_narrow_req_out_valid;
  `endif
  // wide req noc
  floo_tcdm_rdwr_req_t  [NumX-1:0][NumY-1:0][West:North][NumTilesPerGroup-1:0][NumWideRemoteReqPortsPerTile-1:0]   floo_tcdm_wide_req_in;
  logic                 [NumX-1:0][NumY-1:0][West:North][NumTilesPerGroup-1:0][NumWideRemoteReqPortsPerTile-1:0][NumVirtualChannel-1:0]   floo_tcdm_wide_req_in_ready, floo_tcdm_wide_req_in_valid;
  floo_tcdm_rdwr_req_t  [NumX-1:0][NumY-1:0][West:North][NumTilesPerGroup-1:0][NumWideRemoteReqPortsPerTile-1:0]   floo_tcdm_wide_req_out;
  logic                 [NumX-1:0][NumY-1:0][West:North][NumTilesPerGroup-1:0][NumWideRemoteReqPortsPerTile-1:0][NumVirtualChannel-1:0]   floo_tcdm_wide_req_out_ready, floo_tcdm_wide_req_out_valid;
  // wide resp noc
  floo_tcdm_resp_t      [NumX-1:0][NumY-1:0][West:North][NumTilesPerGroup-1:0][NumRemoteRespPortsPerTile-1:1]      floo_tcdm_resp_in;
  logic                 [NumX-1:0][NumY-1:0][West:North][NumTilesPerGroup-1:0][NumRemoteRespPortsPerTile-1:1][NumVirtualChannel-1:0]      floo_tcdm_resp_in_ready, floo_tcdm_resp_in_valid;
  floo_tcdm_resp_t      [NumX-1:0][NumY-1:0][West:North][NumTilesPerGroup-1:0][NumRemoteRespPortsPerTile-1:1]      floo_tcdm_resp_out;
  logic                 [NumX-1:0][NumY-1:0][West:North][NumTilesPerGroup-1:0][NumRemoteRespPortsPerTile-1:1][NumVirtualChannel-1:0]      floo_tcdm_resp_out_ready, floo_tcdm_resp_out_valid;

  floo_terapool_noc_pkg::floo_req_t  [NumX-1:0][NumY-1:0][West:North] floo_axi_req_out, floo_axi_req_in;
  floo_terapool_noc_pkg::floo_rsp_t  [NumX-1:0][NumY-1:0][West:North] floo_axi_rsp_out, floo_axi_rsp_in;
  floo_terapool_noc_pkg::floo_wide_t [NumX-1:0][NumY-1:0][West:North] floo_axi_wide_out, floo_axi_wide_in;

  localparam floo_pkg::chimney_cfg_t ChimneyCfgN = floo_pkg::set_ports(floo_pkg::ChimneyDefaultCfg, 1'b0, 1'b0);
  localparam floo_pkg::chimney_cfg_t ChimneyCfgW = floo_pkg::set_ports(floo_pkg::ChimneyDefaultCfg, 1'b1, 1'b0);

  for (genvar x = 0; x < NumX; x++) begin : gen_groups_x
    for (genvar y = 0; y < NumY; y++) begin : gen_groups_y
      group_xy_id_t group_id;
      assign group_id = '{x:x, y:y, port_id:1'b0};

      // TODO: Add support for Torus Topology
      if (x == 0) begin : gen_hbm_chimney_west
        // West
      `ifdef TORUS
        `ifdef USE_NARROW_REQ_CHANNEL
        assign floo_tcdm_narrow_req_in[x][y][West]           = floo_tcdm_narrow_req_out[NumX-1][y][East];
        assign floo_tcdm_narrow_req_in_valid[x][y][West]     = floo_tcdm_narrow_req_out_valid[NumX-1][y][East];
        assign floo_tcdm_narrow_req_in_ready[x][y][West]     = floo_tcdm_narrow_req_out_ready[NumX-1][y][East];
        `endif
        assign floo_tcdm_wide_req_in[x][y][West]             = floo_tcdm_wide_req_out[NumX-1][y][East];
        assign floo_tcdm_wide_req_in_valid[x][y][West]       = floo_tcdm_wide_req_out_valid[NumX-1][y][East];
        assign floo_tcdm_wide_req_in_ready[x][y][West]       = floo_tcdm_wide_req_out_ready[NumX-1][y][East];
        assign floo_tcdm_resp_in[x][y][West]                 = floo_tcdm_resp_out[NumX-1][y][East];
        assign floo_tcdm_resp_in_valid[x][y][West]           = floo_tcdm_resp_out_valid[NumX-1][y][East];
        assign floo_tcdm_resp_in_ready[x][y][West]           = floo_tcdm_resp_out_ready[NumX-1][y][East];
      `else
        `ifdef USE_NARROW_REQ_CHANNEL
        assign floo_tcdm_narrow_req_in       [x][y][West]  = '0;
        assign floo_tcdm_narrow_req_in_valid [x][y][West]  = '0;
        assign floo_tcdm_narrow_req_in_ready [x][y][West]  = '0;
        `endif
        assign floo_tcdm_wide_req_in         [x][y][West]  = '0;
        assign floo_tcdm_wide_req_in_valid   [x][y][West]  = '0;
        assign floo_tcdm_wide_req_in_ready   [x][y][West]  = '0;
        assign floo_tcdm_resp_in             [x][y][West]  = '0;
        assign floo_tcdm_resp_in_valid       [x][y][West]  = '0;
        assign floo_tcdm_resp_in_ready       [x][y][West]  = '0;
      `endif
        // East
        `ifdef USE_NARROW_REQ_CHANNEL
        assign floo_tcdm_narrow_req_in       [x][y][East]  = floo_tcdm_narrow_req_out       [x+1][y][West];
        assign floo_tcdm_narrow_req_in_valid [x][y][East]  = floo_tcdm_narrow_req_out_valid [x+1][y][West];
        assign floo_tcdm_narrow_req_in_ready [x][y][East]  = floo_tcdm_narrow_req_out_ready [x+1][y][West];
        `endif
        assign floo_tcdm_wide_req_in         [x][y][East]  = floo_tcdm_wide_req_out         [x+1][y][West];
        assign floo_tcdm_wide_req_in_valid   [x][y][East]  = floo_tcdm_wide_req_out_valid   [x+1][y][West];
        assign floo_tcdm_wide_req_in_ready   [x][y][East]  = floo_tcdm_wide_req_out_ready   [x+1][y][West];
        assign floo_tcdm_resp_in             [x][y][East]  = floo_tcdm_resp_out             [x+1][y][West];
        assign floo_tcdm_resp_in_valid       [x][y][East]  = floo_tcdm_resp_out_valid       [x+1][y][West];
        assign floo_tcdm_resp_in_ready       [x][y][East]  = floo_tcdm_resp_out_ready       [x+1][y][West];

        assign floo_axi_req_in               [x][y][East]  = floo_axi_req_out               [x+1][y][West];
        assign floo_axi_rsp_in               [x][y][East]  = floo_axi_rsp_out               [x+1][y][West];
        assign floo_axi_wide_in              [x][y][East]  = floo_axi_wide_out              [x+1][y][West];

        floo_nw_chimney #(
          .AxiCfgN              ( AxiCfgN               ),
          .AxiCfgW              ( AxiCfgW               ),
          .ChimneyCfgN          ( ChimneyCfgN           ),
          .ChimneyCfgW          ( ChimneyCfgW           ),
          .RouteCfg             ( RouteCfg              ),
          .id_t                 ( id_t                  ),
          .rob_idx_t            ( rob_idx_t             ),
          .route_t              ( route_t               ),
          .dst_t                ( route_t               ),
          .hdr_t                ( hdr_t                 ),
          .sam_rule_t           ( sam_rule_t            ),
          .Sam                  ( Sam                   ),
          .axi_narrow_in_req_t  ( axi_narrow_in_req_t   ),
          .axi_narrow_in_rsp_t  ( axi_narrow_in_rsp_t   ),
          .axi_narrow_out_req_t ( axi_narrow_out_req_t  ),
          .axi_narrow_out_rsp_t ( axi_narrow_out_rsp_t  ),
          .axi_wide_in_req_t    ( axi_wide_in_req_t     ),
          .axi_wide_in_rsp_t    ( axi_wide_in_rsp_t     ),
          .axi_wide_out_req_t   ( axi_wide_out_req_t    ),
          .axi_wide_out_rsp_t   ( axi_wide_out_rsp_t    ),
          .floo_req_t           ( floo_req_t            ),
          .floo_rsp_t           ( floo_rsp_t            ),
          .floo_wide_t          ( floo_wide_t           )
        ) i_floo_nw_chimney (
          .clk_i,
          .rst_ni,
          .test_enable_i        ( testmode_i                    ),
          .sram_cfg_i           ( '0                            ),
          .axi_narrow_in_req_i  ( '0                            ),
          .axi_narrow_in_rsp_o  (                               ),
          .axi_narrow_out_req_o (                               ),
          .axi_narrow_out_rsp_i ( '0                            ),
          .axi_wide_in_req_i    ( '0                            ),
          .axi_wide_in_rsp_o    (                               ),
          .axi_wide_out_req_o   ( axi_mst_req_o[y]              ),
          .axi_wide_out_rsp_i   ( axi_mst_resp_i[y]             ),
          .id_i                 ( id_t'(HbmNi0+y)               ),
          .route_table_i        ( RoutingTables[HbmNi0+y]       ),
          .floo_req_o           ( floo_axi_req_in[x][y][West]   ),
          .floo_rsp_o           ( floo_axi_rsp_in[x][y][West]   ),
          .floo_wide_o          ( floo_axi_wide_in[x][y][West]  ),
          .floo_req_i           ( floo_axi_req_out[x][y][West]  ),
          .floo_rsp_i           ( floo_axi_rsp_out[x][y][West]  ),
          .floo_wide_i          ( floo_axi_wide_out[x][y][West] )
        );
      end else if (x == NumX-1) begin : gen_hbm_chimney_east
        // East
      `ifdef TORUS
        `ifdef USE_NARROW_REQ_CHANNEL
        assign floo_tcdm_narrow_req_in[x][y][East]           = floo_tcdm_narrow_req_out[0][y][West];
        assign floo_tcdm_narrow_req_in_valid[x][y][East]     = floo_tcdm_narrow_req_out_valid[0][y][West];
        assign floo_tcdm_narrow_req_in_ready[x][y][East]     = floo_tcdm_narrow_req_out_ready[0][y][West];
        `endif
        assign floo_tcdm_wide_req_in[x][y][East]             = floo_tcdm_wide_req_out[0][y][West];
        assign floo_tcdm_wide_req_in_valid[x][y][East]       = floo_tcdm_wide_req_out_valid[0][y][West];
        assign floo_tcdm_wide_req_in_ready[x][y][East]       = floo_tcdm_wide_req_out_ready[0][y][West];
        assign floo_tcdm_resp_in[x][y][East]                 = floo_tcdm_resp_out[0][y][West];
        assign floo_tcdm_resp_in_valid[x][y][East]           = floo_tcdm_resp_out_valid[0][y][West];
        assign floo_tcdm_resp_in_ready[x][y][East]           = floo_tcdm_resp_out_ready[0][y][West];
      `else
        `ifdef USE_NARROW_REQ_CHANNEL
        assign floo_tcdm_narrow_req_in       [x][y][East]  = '0;
        assign floo_tcdm_narrow_req_in_valid [x][y][East]  = '0;
        assign floo_tcdm_narrow_req_in_ready [x][y][East]  = '0;
        `endif
        assign floo_tcdm_wide_req_in         [x][y][East]  = '0;
        assign floo_tcdm_wide_req_in_valid   [x][y][East]  = '0;
        assign floo_tcdm_wide_req_in_ready   [x][y][East]  = '0;
        assign floo_tcdm_resp_in             [x][y][East]  = '0;
        assign floo_tcdm_resp_in_valid       [x][y][East]  = '0;
        assign floo_tcdm_resp_in_ready       [x][y][East]  = '0;
      `endif
        // West
        `ifdef USE_NARROW_REQ_CHANNEL
        assign floo_tcdm_narrow_req_in       [x][y][West]  = floo_tcdm_narrow_req_out       [x-1][y][East];
        assign floo_tcdm_narrow_req_in_valid [x][y][West]  = floo_tcdm_narrow_req_out_valid [x-1][y][East];
        assign floo_tcdm_narrow_req_in_ready [x][y][West]  = floo_tcdm_narrow_req_out_ready [x-1][y][East];
        `endif
        assign floo_tcdm_wide_req_in         [x][y][West]  = floo_tcdm_wide_req_out         [x-1][y][East];
        assign floo_tcdm_wide_req_in_valid   [x][y][West]  = floo_tcdm_wide_req_out_valid   [x-1][y][East];
        assign floo_tcdm_wide_req_in_ready   [x][y][West]  = floo_tcdm_wide_req_out_ready   [x-1][y][East];
        assign floo_tcdm_resp_in             [x][y][West]  = floo_tcdm_resp_out             [x-1][y][East];
        assign floo_tcdm_resp_in_valid       [x][y][West]  = floo_tcdm_resp_out_valid       [x-1][y][East];
        assign floo_tcdm_resp_in_ready       [x][y][West]  = floo_tcdm_resp_out_ready       [x-1][y][East];

        assign floo_axi_req_in               [x][y][West]  = floo_axi_req_out               [x-1][y][East];
        assign floo_axi_rsp_in               [x][y][West]  = floo_axi_rsp_out               [x-1][y][East];
        assign floo_axi_wide_in              [x][y][West]  = floo_axi_wide_out              [x-1][y][East];

        floo_nw_chimney #(
          .AxiCfgN              ( AxiCfgN               ),
          .AxiCfgW              ( AxiCfgW               ),
          .ChimneyCfgN          ( ChimneyCfgN           ),
          .ChimneyCfgW          ( ChimneyCfgW           ),
          .RouteCfg             ( RouteCfg              ),
          .id_t                 ( id_t                  ),
          .rob_idx_t            ( rob_idx_t             ),
          .route_t              ( route_t               ),
          .dst_t                ( route_t               ),
          .hdr_t                ( hdr_t                 ),
          .sam_rule_t           ( sam_rule_t            ),
          .Sam                  ( Sam                   ),
          .axi_narrow_in_req_t  ( axi_narrow_in_req_t   ),
          .axi_narrow_in_rsp_t  ( axi_narrow_in_rsp_t   ),
          .axi_narrow_out_req_t ( axi_narrow_out_req_t  ),
          .axi_narrow_out_rsp_t ( axi_narrow_out_rsp_t  ),
          .axi_wide_in_req_t    ( axi_wide_in_req_t     ),
          .axi_wide_in_rsp_t    ( axi_wide_in_rsp_t     ),
          .axi_wide_out_req_t   ( axi_wide_out_req_t    ),
          .axi_wide_out_rsp_t   ( axi_wide_out_rsp_t    ),
          .floo_req_t           ( floo_req_t            ),
          .floo_rsp_t           ( floo_rsp_t            ),
          .floo_wide_t          ( floo_wide_t           )
        ) i_floo_nw_chimney (
          .clk_i,
          .rst_ni,
          .test_enable_i        ( testmode_i                    ),
          .sram_cfg_i           ( '0                            ),
          .axi_narrow_in_req_i  ( '0                            ),
          .axi_narrow_in_rsp_o  (                               ),
          .axi_narrow_out_req_o (                               ),
          .axi_narrow_out_rsp_i ( '0                            ),
          .axi_wide_in_req_i    ( '0                            ),
          .axi_wide_in_rsp_o    (                               ),
          .axi_wide_out_req_o   ( axi_mst_req_o[y+12]           ),
          .axi_wide_out_rsp_i   ( axi_mst_resp_i[y+12]          ),
          .id_i                 ( id_t'(HbmNi12+y)              ),
          .route_table_i        ( RoutingTables[HbmNi12+y]      ),
          .floo_req_o           ( floo_axi_req_in[x][y][East]   ),
          .floo_rsp_o           ( floo_axi_rsp_in[x][y][East]   ),
          .floo_wide_o          ( floo_axi_wide_in[x][y][East]  ),
          .floo_req_i           ( floo_axi_req_out[x][y][East]  ),
          .floo_rsp_i           ( floo_axi_rsp_out[x][y][East]  ),
          .floo_wide_i          ( floo_axi_wide_out[x][y][East] )
        );
      end else begin : gen_hor_connections
        // East
        `ifdef USE_NARROW_REQ_CHANNEL
        assign floo_tcdm_narrow_req_in       [x][y][East]  = floo_tcdm_narrow_req_out       [x+1][y][West];
        assign floo_tcdm_narrow_req_in_valid [x][y][East]  = floo_tcdm_narrow_req_out_valid [x+1][y][West];
        assign floo_tcdm_narrow_req_in_ready [x][y][East]  = floo_tcdm_narrow_req_out_ready [x+1][y][West];
        `endif
        assign floo_tcdm_wide_req_in         [x][y][East]  = floo_tcdm_wide_req_out         [x+1][y][West];
        assign floo_tcdm_wide_req_in_valid   [x][y][East]  = floo_tcdm_wide_req_out_valid   [x+1][y][West];
        assign floo_tcdm_wide_req_in_ready   [x][y][East]  = floo_tcdm_wide_req_out_ready   [x+1][y][West];
        assign floo_tcdm_resp_in             [x][y][East]  = floo_tcdm_resp_out             [x+1][y][West];
        assign floo_tcdm_resp_in_valid       [x][y][East]  = floo_tcdm_resp_out_valid       [x+1][y][West];
        assign floo_tcdm_resp_in_ready       [x][y][East]  = floo_tcdm_resp_out_ready       [x+1][y][West];

        assign floo_axi_req_in               [x][y][East]  = floo_axi_req_out               [x+1][y][West];
        assign floo_axi_rsp_in               [x][y][East]  = floo_axi_rsp_out               [x+1][y][West];
        assign floo_axi_wide_in              [x][y][East]  = floo_axi_wide_out              [x+1][y][West];
        // West
        `ifdef USE_NARROW_REQ_CHANNEL
        assign floo_tcdm_narrow_req_in       [x][y][West]  = floo_tcdm_narrow_req_out       [x-1][y][East];
        assign floo_tcdm_narrow_req_in_valid [x][y][West]  = floo_tcdm_narrow_req_out_valid [x-1][y][East];
        assign floo_tcdm_narrow_req_in_ready [x][y][West]  = floo_tcdm_narrow_req_out_ready [x-1][y][East];
        `endif
        assign floo_tcdm_wide_req_in         [x][y][West]  = floo_tcdm_wide_req_out         [x-1][y][East];
        assign floo_tcdm_wide_req_in_valid   [x][y][West]  = floo_tcdm_wide_req_out_valid   [x-1][y][East];
        assign floo_tcdm_wide_req_in_ready   [x][y][West]  = floo_tcdm_wide_req_out_ready   [x-1][y][East];
        assign floo_tcdm_resp_in             [x][y][West]  = floo_tcdm_resp_out             [x-1][y][East];
        assign floo_tcdm_resp_in_valid       [x][y][West]  = floo_tcdm_resp_out_valid       [x-1][y][East];
        assign floo_tcdm_resp_in_ready       [x][y][West]  = floo_tcdm_resp_out_ready       [x-1][y][East];

        assign floo_axi_req_in               [x][y][West]  = floo_axi_req_out               [x-1][y][East];
        assign floo_axi_rsp_in               [x][y][West]  = floo_axi_rsp_out               [x-1][y][East];
        assign floo_axi_wide_in              [x][y][West]  = floo_axi_wide_out              [x-1][y][East];
      end

      if (y == 0) begin : gen_hbm_chimney_south
        // South
      `ifdef TORUS
        `ifdef USE_NARROW_REQ_CHANNEL
        assign floo_tcdm_narrow_req_in[x][y][South]          = floo_tcdm_narrow_req_out[x][NumY-1][North];
        assign floo_tcdm_narrow_req_in_valid[x][y][South]    = floo_tcdm_narrow_req_out_valid[x][NumY-1][North];
        assign floo_tcdm_narrow_req_in_ready[x][y][South]    = floo_tcdm_narrow_req_out_ready[x][NumY-1][North];
        `endif
        assign floo_tcdm_wide_req_in[x][y][South]            = floo_tcdm_wide_req_out[x][NumY-1][North];
        assign floo_tcdm_wide_req_in_valid[x][y][South]      = floo_tcdm_wide_req_out_valid[x][NumY-1][North];
        assign floo_tcdm_wide_req_in_ready[x][y][South]      = floo_tcdm_wide_req_out_ready[x][NumY-1][North];
        assign floo_tcdm_resp_in[x][y][South]                = floo_tcdm_resp_out[x][NumY-1][North];
        assign floo_tcdm_resp_in_valid[x][y][South]          = floo_tcdm_resp_out_valid[x][NumY-1][North];
        assign floo_tcdm_resp_in_ready[x][y][South]          = floo_tcdm_resp_out_ready[x][NumY-1][North];
      `else
        `ifdef USE_NARROW_REQ_CHANNEL
        assign floo_tcdm_narrow_req_in       [x][y][South] = '0;
        assign floo_tcdm_narrow_req_in_valid [x][y][South] = '0;
        assign floo_tcdm_narrow_req_in_ready [x][y][South] = '0;
        `endif
        assign floo_tcdm_wide_req_in         [x][y][South] = '0;
        assign floo_tcdm_wide_req_in_valid   [x][y][South] = '0;
        assign floo_tcdm_wide_req_in_ready   [x][y][South] = '0;
        assign floo_tcdm_resp_in             [x][y][South] = '0;
        assign floo_tcdm_resp_in_valid       [x][y][South] = '0;
        assign floo_tcdm_resp_in_ready       [x][y][South] = '0;
      `endif
        // North
        `ifdef USE_NARROW_REQ_CHANNEL
        assign floo_tcdm_narrow_req_in       [x][y][North] = floo_tcdm_narrow_req_out       [x][y+1][South];
        assign floo_tcdm_narrow_req_in_valid [x][y][North] = floo_tcdm_narrow_req_out_valid [x][y+1][South];
        assign floo_tcdm_narrow_req_in_ready [x][y][North] = floo_tcdm_narrow_req_out_ready [x][y+1][South];
        `endif
        assign floo_tcdm_wide_req_in         [x][y][North] = floo_tcdm_wide_req_out         [x][y+1][South];
        assign floo_tcdm_wide_req_in_valid   [x][y][North] = floo_tcdm_wide_req_out_valid   [x][y+1][South];
        assign floo_tcdm_wide_req_in_ready   [x][y][North] = floo_tcdm_wide_req_out_ready   [x][y+1][South];
        assign floo_tcdm_resp_in             [x][y][North] = floo_tcdm_resp_out             [x][y+1][South];
        assign floo_tcdm_resp_in_valid       [x][y][North] = floo_tcdm_resp_out_valid       [x][y+1][South];
        assign floo_tcdm_resp_in_ready       [x][y][North] = floo_tcdm_resp_out_ready       [x][y+1][South];

        assign floo_axi_req_in               [x][y][North] = floo_axi_req_out               [x][y+1][South];
        assign floo_axi_rsp_in               [x][y][North] = floo_axi_rsp_out               [x][y+1][South];
        assign floo_axi_wide_in              [x][y][North] = floo_axi_wide_out              [x][y+1][South];

        if (x == 1) begin : gen_normal_chimneys

          floo_nw_chimney #(
            .AxiCfgN              ( AxiCfgN               ),
            .AxiCfgW              ( AxiCfgW               ),
            .ChimneyCfgN          ( ChimneyCfgN           ),
            .ChimneyCfgW          ( ChimneyCfgW           ),
            .RouteCfg             ( RouteCfg              ),
            .id_t                 ( id_t                  ),
            .rob_idx_t            ( rob_idx_t             ),
            .route_t              ( route_t               ),
            .dst_t                ( route_t               ),
            .hdr_t                ( hdr_t                 ),
            .sam_rule_t           ( sam_rule_t            ),
            .Sam                  ( Sam                   ),
            .axi_narrow_in_req_t  ( axi_narrow_in_req_t   ),
            .axi_narrow_in_rsp_t  ( axi_narrow_in_rsp_t   ),
            .axi_narrow_out_req_t ( axi_narrow_out_req_t  ),
            .axi_narrow_out_rsp_t ( axi_narrow_out_rsp_t  ),
            .axi_wide_in_req_t    ( axi_wide_in_req_t     ),
            .axi_wide_in_rsp_t    ( axi_wide_in_rsp_t     ),
            .axi_wide_out_req_t   ( axi_wide_out_req_t    ),
            .axi_wide_out_rsp_t   ( axi_wide_out_rsp_t    ),
            .floo_req_t           ( floo_req_t            ),
            .floo_rsp_t           ( floo_rsp_t            ),
            .floo_wide_t          ( floo_wide_t           )
          ) i_floo_nw_chimney (
            .clk_i,
            .rst_ni,
            .test_enable_i        ( testmode_i                    ),
            .sram_cfg_i           ( '0                            ),
            .axi_narrow_in_req_i  ( '0                            ),
            .axi_narrow_in_rsp_o  (                               ),
            .axi_narrow_out_req_o (                               ),
            .axi_narrow_out_rsp_i ( '0                            ),
            .axi_wide_in_req_i    ( '0                            ),
            .axi_wide_in_rsp_o    (                               ),
            .axi_wide_out_req_o   ( axi_mst_req_o[5-x]           ),
            .axi_wide_out_rsp_i   ( axi_mst_resp_i[5-x]          ),
            .id_i                 ( id_t'(HbmNi5-x)              ),
            .route_table_i        ( RoutingTables[HbmNi5-x]      ),
            .floo_req_o           ( floo_axi_req_in[x][y][South]  ),
            .floo_rsp_o           ( floo_axi_rsp_in[x][y][South]  ),
            .floo_wide_o          ( floo_axi_wide_in[x][y][South] ),
            .floo_req_i           ( floo_axi_req_out[x][y][South] ),
            .floo_rsp_i           ( floo_axi_rsp_out[x][y][South] ),
            .floo_wide_i          ( floo_axi_wide_out[x][y][South])
          );
          end
          else if ((x < NumX) && (x != 0)) begin : gen_normal_chimneys_2

          floo_nw_chimney #(
            .AxiCfgN              ( AxiCfgN               ),
            .AxiCfgW              ( AxiCfgW               ),
            .ChimneyCfgN          ( ChimneyCfgN           ),
            .ChimneyCfgW          ( ChimneyCfgW           ),
            .RouteCfg             ( RouteCfg              ),
            .id_t                 ( id_t                  ),
            .rob_idx_t            ( rob_idx_t             ),
            .route_t              ( route_t               ),
            .dst_t                ( route_t               ),
            .hdr_t                ( hdr_t                 ),
            .sam_rule_t           ( sam_rule_t            ),
            .Sam                  ( Sam                   ),
            .axi_narrow_in_req_t  ( axi_narrow_in_req_t   ),
            .axi_narrow_in_rsp_t  ( axi_narrow_in_rsp_t   ),
            .axi_narrow_out_req_t ( axi_narrow_out_req_t  ),
            .axi_narrow_out_rsp_t ( axi_narrow_out_rsp_t  ),
            .axi_wide_in_req_t    ( axi_wide_in_req_t     ),
            .axi_wide_in_rsp_t    ( axi_wide_in_rsp_t     ),
            .axi_wide_out_req_t   ( axi_wide_out_req_t    ),
            .axi_wide_out_rsp_t   ( axi_wide_out_rsp_t    ),
            .floo_req_t           ( floo_req_t            ),
            .floo_rsp_t           ( floo_rsp_t            ),
            .floo_wide_t          ( floo_wide_t           )
          ) i_floo_nw_chimney (
            .clk_i,
            .rst_ni,
            .test_enable_i        ( testmode_i                    ),
            .sram_cfg_i           ( '0                            ),
            .axi_narrow_in_req_i  ( '0                            ),
            .axi_narrow_in_rsp_o  (                               ),
            .axi_narrow_out_req_o (                               ),
            .axi_narrow_out_rsp_i ( '0                            ),
            .axi_wide_in_req_i    ( '0                            ),
            .axi_wide_in_rsp_o    (                               ),
            .axi_wide_out_req_o   ( axi_mst_req_o[x+6]           ),
            .axi_wide_out_rsp_i   ( axi_mst_resp_i[x+6]          ),
            .id_i                 ( id_t'(HbmNi6+x)              ),
            .route_table_i        ( RoutingTables[HbmNi6+x]      ),
            .floo_req_o           ( floo_axi_req_in[x][y][South]  ),
            .floo_rsp_o           ( floo_axi_rsp_in[x][y][South]  ),
            .floo_wide_o          ( floo_axi_wide_in[x][y][South] ),
            .floo_req_i           ( floo_axi_req_out[x][y][South] ),
            .floo_rsp_i           ( floo_axi_rsp_out[x][y][South] ),
            .floo_wide_i          ( floo_axi_wide_out[x][y][South])
          );
        end else begin

          floo_req_t  [3:0] periph_router_req_in;
          floo_rsp_t  [3:0] periph_router_rsp_out;
          floo_req_t  [3:0] periph_router_req_out;
          floo_rsp_t  [3:0] periph_router_rsp_in;
          floo_wide_t [3:0] periph_router_wide_in;
          floo_wide_t [3:0] periph_router_wide_out;

          assign periph_router_req_in[0] = floo_axi_req_out[x][y][South];
          assign periph_router_rsp_in[0] = floo_axi_rsp_out[x][y][South];
          assign periph_router_wide_in[0] = floo_axi_wide_out[x][y][South];
          assign floo_axi_req_in[x][y][South] = periph_router_req_out[0];
          assign floo_axi_rsp_in[x][y][South] = periph_router_rsp_out[0];
          assign floo_axi_wide_in[x][y][South] = periph_router_wide_out[0];

          floo_nw_router #(
            .AxiCfgN      ( AxiCfgN             ),
            .AxiCfgW      ( AxiCfgW             ),
            .RouteAlgo    ( RouteCfg.RouteAlgo  ),
            .NumRoutes    ( 4                   ),
            .InFifoDepth  ( 2                   ),
            .OutFifoDepth ( 2                   ),
            .id_t         ( id_t                ),
            .hdr_t        ( hdr_t               ),
            .floo_req_t   ( floo_req_t          ),
            .floo_rsp_t   ( floo_rsp_t          ),
            .floo_wide_t  ( floo_wide_t         )
          ) periph_router (
            .clk_i,
            .rst_ni,
            .test_enable_i  ( testmode_i              ),
            .id_i           ( '0                      ),
            .id_route_map_i ( '0                      ),
            .floo_req_i     ( periph_router_req_in    ),
            .floo_rsp_o     ( periph_router_rsp_out   ),
            .floo_req_o     ( periph_router_req_out   ),
            .floo_rsp_i     ( periph_router_rsp_in    ),
            .floo_wide_i    ( periph_router_wide_in   ),
            .floo_wide_o    ( periph_router_wide_out  )
          );

          floo_nw_chimney #(
            .AxiCfgN              ( AxiCfgN               ),
            .AxiCfgW              ( AxiCfgW               ),
            .ChimneyCfgN          ( ChimneyCfgN           ),
            .ChimneyCfgW          ( ChimneyCfgW           ),
            .RouteCfg             ( RouteCfg              ),
            .id_t                 ( id_t                  ),
            .rob_idx_t            ( rob_idx_t             ),
            .route_t              ( route_t               ),
            .dst_t                ( route_t               ),
            .hdr_t                ( hdr_t                 ),
            .sam_rule_t           ( sam_rule_t            ),
            .Sam                  ( Sam                   ),
            .axi_narrow_in_req_t  ( axi_narrow_in_req_t   ),
            .axi_narrow_in_rsp_t  ( axi_narrow_in_rsp_t   ),
            .axi_narrow_out_req_t ( axi_narrow_out_req_t  ),
            .axi_narrow_out_rsp_t ( axi_narrow_out_rsp_t  ),
            .axi_wide_in_req_t    ( axi_wide_in_req_t     ),
            .axi_wide_in_rsp_t    ( axi_wide_in_rsp_t     ),
            .axi_wide_out_req_t   ( axi_wide_out_req_t    ),
            .axi_wide_out_rsp_t   ( axi_wide_out_rsp_t    ),
            .floo_req_t           ( floo_req_t            ),
            .floo_rsp_t           ( floo_rsp_t            ),
            .floo_wide_t          ( floo_wide_t           )
          ) hbm_ni_15 (
            .clk_i,
            .rst_ni,
            .test_enable_i        ( testmode_i                ),
            .sram_cfg_i           ( '0                        ),
            .axi_narrow_in_req_i  ( '0                        ),
            .axi_narrow_in_rsp_o  (                           ),
            .axi_narrow_out_req_o (                           ),
            .axi_narrow_out_rsp_i ( '0                        ),
            .axi_wide_in_req_i    ( '0                        ),
            .axi_wide_in_rsp_o    (                           ),
            .axi_wide_out_req_o   ( axi_mst_req_o[5]         ),
            .axi_wide_out_rsp_i   ( axi_mst_resp_i[5]        ),
            .id_i                 ( id_t'(HbmNi5)            ),
            .route_table_i        ( RoutingTables[HbmNi5]    ),
            .floo_req_o           ( periph_router_req_in[1]   ),
            .floo_rsp_i           ( periph_router_rsp_out[1]  ),
            .floo_wide_o          ( periph_router_wide_in[1]  ),
            .floo_req_i           ( periph_router_req_out[1]  ),
            .floo_rsp_o           ( periph_router_rsp_in[1]   ),
            .floo_wide_i          ( periph_router_wide_out[1] )
          );

          localparam floo_pkg::chimney_cfg_t PeriphChimneyCfgW = floo_pkg::set_ports(floo_pkg::ChimneyDefaultCfg, 1'b1, 1'b0);

          floo_nw_chimney #(
            .AxiCfgN              ( AxiCfgN               ),
            .AxiCfgW              ( AxiCfgW               ),
            .ChimneyCfgN          ( ChimneyCfgN           ),
            .ChimneyCfgW          ( PeriphChimneyCfgW     ),
            .RouteCfg             ( RouteCfg              ),
            .id_t                 ( id_t                  ),
            .rob_idx_t            ( rob_idx_t             ),
            .route_t              ( route_t               ),
            .dst_t                ( route_t               ),
            .hdr_t                ( hdr_t                 ),
            .sam_rule_t           ( sam_rule_t            ),
            .Sam                  ( Sam                   ),
            .axi_narrow_in_req_t  ( axi_narrow_in_req_t   ),
            .axi_narrow_in_rsp_t  ( axi_narrow_in_rsp_t   ),
            .axi_narrow_out_req_t ( axi_narrow_out_req_t  ),
            .axi_narrow_out_rsp_t ( axi_narrow_out_rsp_t  ),
            .axi_wide_in_req_t    ( axi_wide_in_req_t     ),
            .axi_wide_in_rsp_t    ( axi_wide_in_rsp_t     ),
            .axi_wide_out_req_t   ( axi_wide_out_req_t    ),
            .axi_wide_out_rsp_t   ( axi_wide_out_rsp_t    ),
            .floo_req_t           ( floo_req_t            ),
            .floo_rsp_t           ( floo_rsp_t            ),
            .floo_wide_t          ( floo_wide_t           )
          ) peripherals_ni (
            .clk_i,
            .rst_ni,
            .test_enable_i        ( testmode_i                    ),
            .sram_cfg_i           ( '0                            ),
            .axi_narrow_in_req_i  ( '0                            ),
            .axi_narrow_in_rsp_o  (                               ),
            .axi_narrow_out_req_o (                               ),
            .axi_narrow_out_rsp_i ( '0                            ),
            .axi_wide_in_req_i    ( '0                            ),
            .axi_wide_in_rsp_o    (                               ),
            .axi_wide_out_req_o   ( periph_mst_req_o              ),
            .axi_wide_out_rsp_i   ( periph_mst_resp_i             ),
            .id_i                 ( id_t'(PeripheralsNi)          ),
            .route_table_i        ( RoutingTables[PeripheralsNi]  ),
            .floo_req_o           ( periph_router_req_in[2]       ),
            .floo_rsp_i           ( periph_router_rsp_out[2]      ),
            .floo_wide_o          ( periph_router_wide_in[2]      ),
            .floo_req_i           ( periph_router_req_out[2]      ),
            .floo_rsp_o           ( periph_router_rsp_in[2]       ),
            .floo_wide_i          ( periph_router_wide_out[2]     )
        );

        localparam floo_pkg::chimney_cfg_t HostChimneyCfgW = floo_pkg::set_ports(floo_pkg::ChimneyDefaultCfg, 1'b0, 1'b1);

        floo_nw_chimney #(
            .AxiCfgN              ( AxiCfgN               ),
            .AxiCfgW              ( AxiCfgW               ),
            .ChimneyCfgN          ( ChimneyCfgN           ),
            .ChimneyCfgW          ( HostChimneyCfgW       ),
            .RouteCfg             ( RouteCfg              ),
            .id_t                 ( id_t                  ),
            .rob_idx_t            ( rob_idx_t             ),
            .route_t              ( route_t               ),
            .dst_t                ( route_t               ),
            .hdr_t                ( hdr_t                 ),
            .sam_rule_t           ( sam_rule_t            ),
            .Sam                  ( Sam                   ),
            .axi_narrow_in_req_t  ( axi_narrow_in_req_t   ),
            .axi_narrow_in_rsp_t  ( axi_narrow_in_rsp_t   ),
            .axi_narrow_out_req_t ( axi_narrow_out_req_t  ),
            .axi_narrow_out_rsp_t ( axi_narrow_out_rsp_t  ),
            .axi_wide_in_req_t    ( axi_wide_in_req_t     ),
            .axi_wide_in_rsp_t    ( axi_wide_in_rsp_t     ),
            .axi_wide_out_req_t   ( axi_wide_out_req_t    ),
            .axi_wide_out_rsp_t   ( axi_wide_out_rsp_t    ),
            .floo_req_t           ( floo_req_t            ),
            .floo_rsp_t           ( floo_rsp_t            ),
            .floo_wide_t          ( floo_wide_t           )
          ) host_ni (
            .clk_i,
            .rst_ni,
            .test_enable_i        ( testmode_i                    ),
            .sram_cfg_i           ( '0                            ),
            .axi_narrow_in_req_i  ( '0                            ),
            .axi_narrow_in_rsp_o  (                               ),
            .axi_narrow_out_req_o (                               ),
            .axi_narrow_out_rsp_i ( '0                            ),
            .axi_wide_in_req_i    ( host_slv_req_i                ),
            .axi_wide_in_rsp_o    ( host_slv_resp_o               ),
            .axi_wide_out_req_o   (                               ),
            .axi_wide_out_rsp_i   ( '0                            ),
            .id_i                 ( id_t'(HostNi)                 ),
            .route_table_i        ( RoutingTables[HostNi]         ),
            .floo_req_o           ( periph_router_req_in[3]       ),
            .floo_rsp_i           ( periph_router_rsp_out[3]      ),
            .floo_wide_o          ( periph_router_wide_in[3]      ),
            .floo_req_i           ( periph_router_req_out[3]      ),
            .floo_rsp_o           ( periph_router_rsp_in[3]       ),
            .floo_wide_i          ( periph_router_wide_out[3]     )
        );

        end
      end
      else if (y == NumY-1) begin
        // North
      `ifdef TORUS
        `ifdef USE_NARROW_REQ_CHANNEL
        assign floo_tcdm_narrow_req_in[x][y][North]          = floo_tcdm_narrow_req_out[x][0][South];
        assign floo_tcdm_narrow_req_in_valid[x][y][North]    = floo_tcdm_narrow_req_out_valid[x][0][South];
        assign floo_tcdm_narrow_req_in_ready[x][y][North]    = floo_tcdm_narrow_req_out_ready[x][0][South];
        `endif
        assign floo_tcdm_wide_req_in[x][y][North]            = floo_tcdm_wide_req_out[x][0][South];
        assign floo_tcdm_wide_req_in_valid[x][y][North]      = floo_tcdm_wide_req_out_valid[x][0][South];
        assign floo_tcdm_wide_req_in_ready[x][y][North]      = floo_tcdm_wide_req_out_ready[x][0][South];
        assign floo_tcdm_resp_in[x][y][North]                = floo_tcdm_resp_out[x][0][South];
        assign floo_tcdm_resp_in_valid[x][y][North]          = floo_tcdm_resp_out_valid[x][0][South];
        assign floo_tcdm_resp_in_ready[x][y][North]          = floo_tcdm_resp_out_ready[x][0][South];
      `else
        `ifdef USE_NARROW_REQ_CHANNEL
        assign floo_tcdm_narrow_req_in       [x][y][North] = '0;
        assign floo_tcdm_narrow_req_in_valid [x][y][North] = '0;
        assign floo_tcdm_narrow_req_in_ready [x][y][North] = '0;
        `endif
        assign floo_tcdm_wide_req_in         [x][y][North] = '0;
        assign floo_tcdm_wide_req_in_valid   [x][y][North] = '0;
        assign floo_tcdm_wide_req_in_ready   [x][y][North] = '0;
        assign floo_tcdm_resp_in             [x][y][North] = '0;
        assign floo_tcdm_resp_in_valid       [x][y][North] = '0;
        assign floo_tcdm_resp_in_ready       [x][y][North] = '0;
      `endif
        // South
        `ifdef USE_NARROW_REQ_CHANNEL
        assign floo_tcdm_narrow_req_in       [x][y][South] = floo_tcdm_narrow_req_out       [x][y-1][North];
        assign floo_tcdm_narrow_req_in_valid [x][y][South] = floo_tcdm_narrow_req_out_valid [x][y-1][North];
        assign floo_tcdm_narrow_req_in_ready [x][y][South] = floo_tcdm_narrow_req_out_ready [x][y-1][North];
        `endif
        assign floo_tcdm_wide_req_in         [x][y][South] = floo_tcdm_wide_req_out         [x][y-1][North];
        assign floo_tcdm_wide_req_in_valid   [x][y][South] = floo_tcdm_wide_req_out_valid   [x][y-1][North];
        assign floo_tcdm_wide_req_in_ready   [x][y][South] = floo_tcdm_wide_req_out_ready   [x][y-1][North];
        assign floo_tcdm_resp_in             [x][y][South] = floo_tcdm_resp_out             [x][y-1][North];
        assign floo_tcdm_resp_in_valid       [x][y][South] = floo_tcdm_resp_out_valid       [x][y-1][North];
        assign floo_tcdm_resp_in_ready       [x][y][South] = floo_tcdm_resp_out_ready       [x][y-1][North];

        assign floo_axi_req_in               [x][y][South] = floo_axi_req_out               [x][y-1][North];
        assign floo_axi_rsp_in               [x][y][South] = floo_axi_rsp_out               [x][y-1][North];
        assign floo_axi_wide_in              [x][y][South] = floo_axi_wide_out              [x][y-1][North];

        if (x < NumX/2) begin
          floo_nw_chimney #(
              .AxiCfgN              ( AxiCfgN               ),
              .AxiCfgW              ( AxiCfgW               ),
              .ChimneyCfgN          ( ChimneyCfgN           ),
              .ChimneyCfgW          ( ChimneyCfgW           ),
              .RouteCfg             ( RouteCfg              ),
              .id_t                 ( id_t                  ),
              .rob_idx_t            ( rob_idx_t             ),
              .route_t              ( route_t               ),
              .dst_t                ( route_t               ),
              .hdr_t                ( hdr_t                 ),
              .sam_rule_t           ( sam_rule_t            ),
              .Sam                  ( Sam                   ),
              .axi_narrow_in_req_t  ( axi_narrow_in_req_t   ),
              .axi_narrow_in_rsp_t  ( axi_narrow_in_rsp_t   ),
              .axi_narrow_out_req_t ( axi_narrow_out_req_t  ),
              .axi_narrow_out_rsp_t ( axi_narrow_out_rsp_t  ),
              .axi_wide_in_req_t    ( axi_wide_in_req_t     ),
              .axi_wide_in_rsp_t    ( axi_wide_in_rsp_t     ),
              .axi_wide_out_req_t   ( axi_wide_out_req_t    ),
              .axi_wide_out_rsp_t   ( axi_wide_out_rsp_t    ),
              .floo_req_t           ( floo_req_t            ),
              .floo_rsp_t           ( floo_rsp_t            ),
              .floo_wide_t          ( floo_wide_t           )
            ) i_floo_nw_chimney (
              .clk_i,
              .rst_ni,
              .test_enable_i        ( testmode_i                    ),
              .sram_cfg_i           ( '0                            ),
              .axi_narrow_in_req_i  ( '0                            ),
              .axi_narrow_in_rsp_o  (                               ),
              .axi_narrow_out_req_o (                               ),
              .axi_narrow_out_rsp_i ( '0                            ),
              .axi_wide_in_req_i    ( '0                            ),
              .axi_wide_in_rsp_o    (                               ),
              .axi_wide_out_req_o   ( axi_mst_req_o[x+6]          ),
              .axi_wide_out_rsp_i   ( axi_mst_resp_i[x+6]         ),
              .id_i                 ( id_t'(HbmNi6+x)               ),
              .route_table_i        ( RoutingTables[HbmNi6+x]       ),
              .floo_req_o           ( floo_axi_req_in[x][y][North]  ),
              .floo_rsp_o           ( floo_axi_rsp_in[x][y][North]  ),
              .floo_wide_o          ( floo_axi_wide_in[x][y][North] ),
              .floo_req_i           ( floo_axi_req_out[x][y][North] ),
              .floo_rsp_i           ( floo_axi_rsp_out[x][y][North] ),
              .floo_wide_i          ( floo_axi_wide_out[x][y][North])
            );
        end else begin
          floo_nw_chimney #(
              .AxiCfgN              ( AxiCfgN               ),
              .AxiCfgW              ( AxiCfgW               ),
              .ChimneyCfgN          ( ChimneyCfgN           ),
              .ChimneyCfgW          ( ChimneyCfgW           ),
              .RouteCfg             ( RouteCfg              ),
              .id_t                 ( id_t                  ),
              .rob_idx_t            ( rob_idx_t             ),
              .route_t              ( route_t               ),
              .dst_t                ( route_t               ),
              .hdr_t                ( hdr_t                 ),
              .sam_rule_t           ( sam_rule_t            ),
              .Sam                  ( Sam                   ),
              .axi_narrow_in_req_t  ( axi_narrow_in_req_t   ),
              .axi_narrow_in_rsp_t  ( axi_narrow_in_rsp_t   ),
              .axi_narrow_out_req_t ( axi_narrow_out_req_t  ),
              .axi_narrow_out_rsp_t ( axi_narrow_out_rsp_t  ),
              .axi_wide_in_req_t    ( axi_wide_in_req_t     ),
              .axi_wide_in_rsp_t    ( axi_wide_in_rsp_t     ),
              .axi_wide_out_req_t   ( axi_wide_out_req_t    ),
              .axi_wide_out_rsp_t   ( axi_wide_out_rsp_t    ),
              .floo_req_t           ( floo_req_t            ),
              .floo_rsp_t           ( floo_rsp_t            ),
              .floo_wide_t          ( floo_wide_t           )
            ) i_floo_nw_chimney (
              .clk_i,
              .rst_ni,
              .test_enable_i        ( testmode_i                    ),
              .sram_cfg_i           ( '0                            ),
              .axi_narrow_in_req_i  ( '0                            ),
              .axi_narrow_in_rsp_o  (                               ),
              .axi_narrow_out_req_o (                               ),
              .axi_narrow_out_rsp_i ( '0                            ),
              .axi_wide_in_req_i    ( '0                            ),
              .axi_wide_in_rsp_o    (                               ),
              .axi_wide_out_req_o   ( axi_mst_req_o[13-x]          ),
              .axi_wide_out_rsp_i   ( axi_mst_resp_i[13-x]         ),
              .id_i                 ( id_t'(HbmNi13-x)               ),
              .route_table_i        ( RoutingTables[HbmNi13-x]       ),
              .floo_req_o           ( floo_axi_req_in[x][y][North]  ),
              .floo_rsp_o           ( floo_axi_rsp_in[x][y][North]  ),
              .floo_wide_o          ( floo_axi_wide_in[x][y][North] ),
              .floo_req_i           ( floo_axi_req_out[x][y][North] ),
              .floo_rsp_i           ( floo_axi_rsp_out[x][y][North] ),
              .floo_wide_i          ( floo_axi_wide_out[x][y][North])
            );
        end
      end
      else begin
        // North
        `ifdef USE_NARROW_REQ_CHANNEL
        assign floo_tcdm_narrow_req_in       [x][y][North] = floo_tcdm_narrow_req_out       [x][y+1][South];
        assign floo_tcdm_narrow_req_in_valid [x][y][North] = floo_tcdm_narrow_req_out_valid [x][y+1][South];
        assign floo_tcdm_narrow_req_in_ready [x][y][North] = floo_tcdm_narrow_req_out_ready [x][y+1][South];
        `endif
        assign floo_tcdm_wide_req_in         [x][y][North] = floo_tcdm_wide_req_out         [x][y+1][South];
        assign floo_tcdm_wide_req_in_valid   [x][y][North] = floo_tcdm_wide_req_out_valid   [x][y+1][South];
        assign floo_tcdm_wide_req_in_ready   [x][y][North] = floo_tcdm_wide_req_out_ready   [x][y+1][South];
        assign floo_tcdm_resp_in             [x][y][North] = floo_tcdm_resp_out             [x][y+1][South];
        assign floo_tcdm_resp_in_valid       [x][y][North] = floo_tcdm_resp_out_valid       [x][y+1][South];
        assign floo_tcdm_resp_in_ready       [x][y][North] = floo_tcdm_resp_out_ready       [x][y+1][South];

        assign floo_axi_req_in               [x][y][North] = floo_axi_req_out               [x][y+1][South];
        assign floo_axi_rsp_in               [x][y][North] = floo_axi_rsp_out               [x][y+1][South];
        assign floo_axi_wide_in              [x][y][North] = floo_axi_wide_out              [x][y+1][South];
        // South
        `ifdef USE_NARROW_REQ_CHANNEL
        assign floo_tcdm_narrow_req_in       [x][y][South] = floo_tcdm_narrow_req_out       [x][y-1][North];
        assign floo_tcdm_narrow_req_in_valid [x][y][South] = floo_tcdm_narrow_req_out_valid [x][y-1][North];
        assign floo_tcdm_narrow_req_in_ready [x][y][South] = floo_tcdm_narrow_req_out_ready [x][y-1][North];
        `endif
        assign floo_tcdm_wide_req_in         [x][y][South] = floo_tcdm_wide_req_out         [x][y-1][North];
        assign floo_tcdm_wide_req_in_valid   [x][y][South] = floo_tcdm_wide_req_out_valid   [x][y-1][North];
        assign floo_tcdm_wide_req_in_ready   [x][y][South] = floo_tcdm_wide_req_out_ready   [x][y-1][North];
        assign floo_tcdm_resp_in             [x][y][South] = floo_tcdm_resp_out             [x][y-1][North];
        assign floo_tcdm_resp_in_valid       [x][y][South] = floo_tcdm_resp_out_valid       [x][y-1][North];
        assign floo_tcdm_resp_in_ready       [x][y][South] = floo_tcdm_resp_out_ready       [x][y-1][North];

        assign floo_axi_req_in               [x][y][South] = floo_axi_req_out               [x][y-1][North];
        assign floo_axi_rsp_in               [x][y][South] = floo_axi_rsp_out               [x][y-1][North];
        assign floo_axi_wide_in              [x][y][South] = floo_axi_wide_out              [x][y-1][North];
      end

      mempool_group_floonoc_wrapper #(
        .TCDMBaseAddr (TCDMBaseAddr         ),
        .BootAddr     (BootAddr             )
      ) i_group (
        .clk_i                          (clk_i                                                           ),
        .rst_ni                         (rst_ni                                                          ),
        .testmode_i                     (testmode_i                                                      ),
        .scan_enable_i                  (scan_enable_i                                                   ),
        .scan_data_i                    (/* Unconnected */                                               ),
        .scan_data_o                    (/* Unconnected */                                               ),
        .group_id_i                     (group_id_t'({group_id.x, group_id.y})                           ),
        .floo_id_i                      (id_t'(GroupNi00 + x*NumY +y)                                    ),
        .route_table_i                  (floo_terapool_noc_pkg::RoutingTables[GroupNi00 + x*NumY +y]     ),
        // TCDM narrow req noc
        `ifdef USE_NARROW_REQ_CHANNEL
        .floo_tcdm_narrow_req_o         (floo_tcdm_narrow_req_out       [x][y]                           ),
        .floo_tcdm_narrow_req_valid_o   (floo_tcdm_narrow_req_out_valid [x][y]                           ),
        .floo_tcdm_narrow_req_ready_i   (floo_tcdm_narrow_req_in_ready  [x][y]                           ),
        .floo_tcdm_narrow_req_i         (floo_tcdm_narrow_req_in        [x][y]                           ),
        .floo_tcdm_narrow_req_valid_i   (floo_tcdm_narrow_req_in_valid  [x][y]                           ),
        .floo_tcdm_narrow_req_ready_o   (floo_tcdm_narrow_req_out_ready [x][y]                           ),
        `endif
        // TCDM wide req noc
        .floo_tcdm_wide_req_o           (floo_tcdm_wide_req_out         [x][y]                           ),
        .floo_tcdm_wide_req_valid_o     (floo_tcdm_wide_req_out_valid   [x][y]                           ),
        .floo_tcdm_wide_req_ready_i     (floo_tcdm_wide_req_in_ready    [x][y]                           ),
        .floo_tcdm_wide_req_i           (floo_tcdm_wide_req_in          [x][y]                           ),
        .floo_tcdm_wide_req_valid_i     (floo_tcdm_wide_req_in_valid    [x][y]                           ),
        .floo_tcdm_wide_req_ready_o     (floo_tcdm_wide_req_out_ready   [x][y]                           ),
        // TCDM resp noc
        .floo_tcdm_resp_o               (floo_tcdm_resp_out             [x][y]                           ),
        .floo_tcdm_resp_valid_o         (floo_tcdm_resp_out_valid       [x][y]                           ),
        .floo_tcdm_resp_ready_i         (floo_tcdm_resp_in_ready        [x][y]                           ),
        .floo_tcdm_resp_i               (floo_tcdm_resp_in              [x][y]                           ),
        .floo_tcdm_resp_valid_i         (floo_tcdm_resp_in_valid        [x][y]                           ),
        .floo_tcdm_resp_ready_o         (floo_tcdm_resp_out_ready       [x][y]                           ),
        .wake_up_i                      (wake_up_q[(NumY*x+y)*NumCoresPerGroup +: NumCoresPerGroup]      ),
        .ro_cache_ctrl_i                (ro_cache_ctrl_q[(NumY*x+y)]                                     ),
        // DMA request
        .dma_req_i                      (dma_req_group_q[(NumY*x+y)]                                     ),
        .dma_req_valid_i                (dma_req_group_q_valid[(NumY*x+y)]                               ),
        .dma_req_ready_o                (dma_req_group_q_ready[(NumY*x+y)]                               ),
        // DMA status
        .dma_meta_o                     (dma_meta[(NumY*x+y)]                                            ),
        // AXI Router interface
        .floo_axi_req_o                 (floo_axi_req_out[x][y]                                          ),
        .floo_axi_rsp_o                 (floo_axi_rsp_out[x][y]                                          ),
        .floo_axi_wide_o                (floo_axi_wide_out[x][y]                                         ),
        .floo_axi_req_i                 (floo_axi_req_in[x][y]                                           ),
        .floo_axi_rsp_i                 (floo_axi_rsp_in[x][y]                                           ),
        .floo_axi_wide_i                (floo_axi_wide_in[x][y]                                          )
      );
    end : gen_groups_y
  end : gen_groups_x

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

endmodule : mempool_cluster_floonoc_wrapper
