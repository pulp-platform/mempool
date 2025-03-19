// Copyright 2024 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "axi/assign.svh"
`include "common_cells/registers.svh"

module mempool_system
  import mempool_pkg::*;
  import cf_math_pkg::idx_width;
  import floo_pkg::*;
  import floo_terapool_noc_pkg::*;
#(
  // TCDM
  parameter addr_t       TCDMBaseAddr  = 32'h0000_0000,
  // Boot address
  parameter addr_t       BootAddr      = 32'h0000_0000
) (
  input logic                clk_i,
  input logic                rst_ni,

  input  logic               fetch_en_i,
  output logic               eoc_valid_o,
  output logic               busy_o,

  output axi_system_req_t    mst_req_o,
  input  axi_system_resp_t   mst_resp_i,

  input  axi_tile_req_t      slv_req_i,
  output axi_tile_resp_t     slv_resp_o
);

  import axi_pkg::xbar_cfg_t;
  import axi_pkg::xbar_rule_32_t;

  /*********
   *  AXI  *
   *********/

  // Overview of AXI buses with SRAM L2
  //
  //      mst_demux
  //        / |
  //       /  | soc  +----------+ periph  +---------+
  //      |  0|=====>| soc_xbar |========>| periph  |
  //  mst |   |      +----------+         +---------+
  // ====>|   |
  //      |   | l2   +----------+  mem    +---------+ bank  +--------+
  //      |  1|=====>| axi2mem  |-------->| l2_xbar |------>| l2_mem |
  //       \  |      +----------+         +---------+       +--------+
  //        \_|
  //                  == axi ==>          -- tcdm -->
  //
  // Overview of AXI buses with DRAM L2
  //
  //      mst_demux
  //        / |
  //       /  | soc  +----------+ periph  +---------+
  //      |  0|=====>| soc_xbar |========>| periph  |
  //  mst |   |      +----------+         +---------+
  // ====>|   |
  //      |   | l2   +----------+  mem_one_port  +--------------+
  //      |  1|=====>| AXI_Mux  |===============>| AXI Port Out |
  //       \  |      +----------+                +--------------+
  //        \_|
  //                  == axi ==>

  localparam NumAXIMasters = NumGroups;
  localparam NumAXISlaves  = 3; // control regs, bootrom and the external mst ports
  localparam NumSoCRules   = NumAXISlaves - 1;

  typedef enum logic [$clog2(NumAXISlaves) - 1:0] {
    Peripherals,
    Bootrom,
    External
  } axi_soc_xbar_slave_target;

  typedef enum logic {
    SoCXBar = 0,
    L2Memory = 1
  } axi_mst_demux_slave_target;

  // From Cluster Interface
  axi_tile_req_t    [NumAXIMasters-1:0] axi_mst_req;
  axi_tile_resp_t   [NumAXIMasters-1:0] axi_mst_resp;
  axi_tile_req_t                        axi_mst_periph_req;
  axi_tile_resp_t                       axi_mst_periph_resp;
  // To System Level Components
  axi_tile_req_t    [NumAXIMasters-1:0] axi_l2_req;
  axi_tile_resp_t   [NumAXIMasters-1:0] axi_l2_resp;
  axi_tile_req_t                        axi_soc_req;
  axi_tile_resp_t                       axi_soc_resp;
  axi_system_req_t  [NumAXISlaves-1:0]  axi_periph_req;
  axi_system_resp_t [NumAXISlaves-1:0]  axi_periph_resp;
  logic             [NumCores-1:0]      wake_up;
  logic             [DataWidth-1:0]     eoc;
  ro_cache_ctrl_t                       ro_cache_ctrl;

  dma_req_t         [NumGroups-1:0]     dma_group_req;
  logic             [NumGroups-1:0]     dma_group_req_valid;
  logic             [NumGroups-1:0]     dma_group_req_ready;
  dma_meta_t        [NumGroups-1:0]     dma_group_meta;

  localparam xbar_cfg_t SoCXBarCfg = '{
    NoSlvPorts         : 1,
    NoMstPorts         : NumAXISlaves,
    MaxMstTrans        : 4,
    MaxSlvTrans        : 4,
    FallThrough        : 1'b0,
    LatencyMode        : axi_pkg::CUT_MST_PORTS,
    PipelineStages     : 0,
    AxiIdWidthSlvPorts : AxiTileIdWidth,
    AxiIdUsedSlvPorts  : AxiTileIdWidth,
    UniqueIds          : 0,
    AxiAddrWidth       : AddrWidth,
    AxiDataWidth       : AxiDataWidth,
    NoAddrRules        : NumSoCRules
  };

  /*********************
   *  MemPool Cluster  *
   ********************/

  localparam floo_pkg::chimney_cfg_t ChimneyCfgN = floo_pkg::set_ports(floo_pkg::ChimneyDefaultCfg, 1'b0, 1'b0);
  localparam floo_pkg::chimney_cfg_t ChimneyCfgW = floo_pkg::set_ports(floo_pkg::ChimneyDefaultCfg, 1'b1, 1'b0);

  `ifdef TERAPOOL
    `define CLUSTER_WRAPPER terapool_cluster_floonoc_wrapper
     // AXI Chimney
     floo_req_t  [NumAXIMasters-1:0] floo_axi_req_in;
     floo_rsp_t  [NumAXIMasters-1:0] floo_axi_rsp_in;
     floo_wide_t [NumAXIMasters-1:0] floo_axi_wide_in;
     floo_req_t  [NumAXIMasters-1:0] floo_axi_req_out;
     floo_rsp_t  [NumAXIMasters-1:0] floo_axi_rsp_out;
     floo_wide_t [NumAXIMasters-1:0] floo_axi_wide_out;
     for (genvar x = 0; x < NumAXIMasters; x++) begin : gen_cluster_axi_chimney
        if (x == 5) begin
          floo_req_t  [3:0] periph_router_req_in;
          floo_rsp_t  [3:0] periph_router_rsp_out;
          floo_req_t  [3:0] periph_router_req_out;
          floo_rsp_t  [3:0] periph_router_rsp_in;
          floo_wide_t [3:0] periph_router_wide_in;
          floo_wide_t [3:0] periph_router_wide_out;

          assign periph_router_req_in[0]  = floo_axi_req_out[x];
          assign periph_router_rsp_in[0]  = floo_axi_rsp_out[x];
          assign periph_router_wide_in[0] = floo_axi_wide_out[x];
          assign floo_axi_req_in[x]       = periph_router_req_out[0];
          assign floo_axi_rsp_in[x]       = periph_router_rsp_out[0];
          assign floo_axi_wide_in[x]      = periph_router_wide_out[0];

          floo_nw_router #(
            .AxiCfgN              ( AxiCfgN                       ),
            .AxiCfgW              ( AxiCfgW                       ),
            .RouteAlgo            ( RouteCfg.RouteAlgo            ),
            .NumRoutes            ( 4                             ),
            .InFifoDepth          ( 2                             ),
            .OutFifoDepth         ( 2                             ),
            .id_t                 ( id_t                          ),
            .hdr_t                ( hdr_t                         ),
            .floo_req_t           ( floo_req_t                    ),
            .floo_rsp_t           ( floo_rsp_t                    ),
            .floo_wide_t          ( floo_wide_t                   ),
            .NumAddrRules         (1                              )
          ) periph_router (
            .clk_i,
            .rst_ni,
            .test_enable_i        ( testmode_i                    ),
            .id_i                 ( '0                            ),
            .id_route_map_i       ( '0                            ),
            .floo_req_i           ( periph_router_req_in          ),
            .floo_rsp_o           ( periph_router_rsp_out         ),
            .floo_req_o           ( periph_router_req_out         ),
            .floo_rsp_i           ( periph_router_rsp_in          ),
            .floo_wide_i          ( periph_router_wide_in         ),
            .floo_wide_o          ( periph_router_wide_out        )
          );

          floo_nw_chimney #(
            .AxiCfgN              ( AxiCfgN                       ),
            .AxiCfgW              ( AxiCfgW                       ),
            .ChimneyCfgN          ( ChimneyCfgN                   ),
            .ChimneyCfgW          ( ChimneyCfgW                   ),
            .AtopSupport          ( '0                            ),
            .RouteCfg             ( RouteCfg                      ),
            .id_t                 ( id_t                          ),
            .rob_idx_t            ( rob_idx_t                     ),
            .route_t              ( route_t                       ),
            .dst_t                ( route_t                       ),
            .hdr_t                ( hdr_t                         ),
            .sam_rule_t           ( sam_rule_t                    ),
            .Sam                  ( Sam                           ),
            .axi_narrow_in_req_t  ( axi_narrow_in_req_t           ),
            .axi_narrow_in_rsp_t  ( axi_narrow_in_rsp_t           ),
            .axi_narrow_out_req_t ( axi_narrow_out_req_t          ),
            .axi_narrow_out_rsp_t ( axi_narrow_out_rsp_t          ),
            .axi_wide_in_req_t    ( axi_wide_in_req_t             ),
            .axi_wide_in_rsp_t    ( axi_wide_in_rsp_t             ),
            .axi_wide_out_req_t   ( axi_wide_out_req_t            ),
            .axi_wide_out_rsp_t   ( axi_wide_out_rsp_t            ),
            .floo_req_t           ( floo_req_t                    ),
            .floo_rsp_t           ( floo_rsp_t                    ),
            .floo_wide_t          ( floo_wide_t                   )
          ) hbm_ni_15 (
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
            .axi_wide_out_req_o   ( axi_mst_req[5]                ),
            .axi_wide_out_rsp_i   ( axi_mst_resp[5]               ),
            .id_i                 ( id_t'(HbmNi5)                 ),
            .route_table_i        ( RoutingTables[HbmNi5]         ),
            .floo_req_o           ( periph_router_req_in[1]       ),
            .floo_rsp_i           ( periph_router_rsp_out[1]      ),
            .floo_wide_o          ( periph_router_wide_in[1]      ),
            .floo_req_i           ( periph_router_req_out[1]      ),
            .floo_rsp_o           ( periph_router_rsp_in[1]       ),
            .floo_wide_i          ( periph_router_wide_out[1]     )
          );

          localparam floo_pkg::chimney_cfg_t PeriphChimneyCfgW = floo_pkg::set_ports(floo_pkg::ChimneyDefaultCfg, 1'b1, 1'b0);
          floo_nw_chimney #(
            .AxiCfgN              ( AxiCfgN                       ),
            .AxiCfgW              ( AxiCfgW                       ),
            .ChimneyCfgN          ( ChimneyCfgN                   ),
            .ChimneyCfgW          ( PeriphChimneyCfgW             ),
            .AtopSupport          ( '0                            ),
            .RouteCfg             ( RouteCfg                      ),
            .id_t                 ( id_t                          ),
            .rob_idx_t            ( rob_idx_t                     ),
            .route_t              ( route_t                       ),
            .dst_t                ( route_t                       ),
            .hdr_t                ( hdr_t                         ),
            .sam_rule_t           ( sam_rule_t                    ),
            .Sam                  ( Sam                           ),
            .axi_narrow_in_req_t  ( axi_narrow_in_req_t           ),
            .axi_narrow_in_rsp_t  ( axi_narrow_in_rsp_t           ),
            .axi_narrow_out_req_t ( axi_narrow_out_req_t          ),
            .axi_narrow_out_rsp_t ( axi_narrow_out_rsp_t          ),
            .axi_wide_in_req_t    ( axi_wide_in_req_t             ),
            .axi_wide_in_rsp_t    ( axi_wide_in_rsp_t             ),
            .axi_wide_out_req_t   ( axi_wide_out_req_t            ),
            .axi_wide_out_rsp_t   ( axi_wide_out_rsp_t            ),
            .floo_req_t           ( floo_req_t                    ),
            .floo_rsp_t           ( floo_rsp_t                    ),
            .floo_wide_t          ( floo_wide_t                   )
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
            .axi_wide_out_req_o   ( axi_mst_periph_req            ),
            .axi_wide_out_rsp_i   ( axi_mst_periph_resp           ),
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
              .AxiCfgN              ( AxiCfgN                     ),
              .AxiCfgW              ( AxiCfgW                     ),
              .ChimneyCfgN          ( ChimneyCfgN                 ),
              .ChimneyCfgW          ( HostChimneyCfgW             ),
              .AtopSupport          ( '0                          ),
              .RouteCfg             ( RouteCfg                    ),
              .id_t                 ( id_t                        ),
              .rob_idx_t            ( rob_idx_t                   ),
              .route_t              ( route_t                     ),
              .dst_t                ( route_t                     ),
              .hdr_t                ( hdr_t                       ),
              .sam_rule_t           ( sam_rule_t                  ),
              .Sam                  ( Sam                         ),
              .axi_narrow_in_req_t  ( axi_narrow_in_req_t         ),
              .axi_narrow_in_rsp_t  ( axi_narrow_in_rsp_t         ),
              .axi_narrow_out_req_t ( axi_narrow_out_req_t        ),
              .axi_narrow_out_rsp_t ( axi_narrow_out_rsp_t        ),
              .axi_wide_in_req_t    ( axi_wide_in_req_t           ),
              .axi_wide_in_rsp_t    ( axi_wide_in_rsp_t           ),
              .axi_wide_out_req_t   ( axi_wide_out_req_t          ),
              .axi_wide_out_rsp_t   ( axi_wide_out_rsp_t          ),
              .floo_req_t           ( floo_req_t                  ),
              .floo_rsp_t           ( floo_rsp_t                  ),
              .floo_wide_t          ( floo_wide_t                 )
            ) host_ni (
              .clk_i,
              .rst_ni,
              .test_enable_i        ( testmode_i                  ),
              .sram_cfg_i           ( '0                          ),
              .axi_narrow_in_req_i  ( '0                          ),
              .axi_narrow_in_rsp_o  (                             ),
              .axi_narrow_out_req_o (                             ),
              .axi_narrow_out_rsp_i ( '0                          ),
              .axi_wide_in_req_i    ( slv_req_i                   ),
              .axi_wide_in_rsp_o    ( slv_resp_o                  ),
              .axi_wide_out_req_o   (                             ),
              .axi_wide_out_rsp_i   ( '0                          ),
              .id_i                 ( id_t'(HostNi)               ),
              .route_table_i        ( RoutingTables[HostNi]       ),
              .floo_req_o           ( periph_router_req_in[3]     ),
              .floo_rsp_i           ( periph_router_rsp_out[3]    ),
              .floo_wide_o          ( periph_router_wide_in[3]    ),
              .floo_req_i           ( periph_router_req_out[3]    ),
              .floo_rsp_o           ( periph_router_rsp_in[3]     ),
              .floo_wide_i          ( periph_router_wide_out[3]   )
          );
        end else begin
          floo_nw_chimney #(
            .AxiCfgN              ( AxiCfgN                       ),
            .AxiCfgW              ( AxiCfgW                       ),
            .ChimneyCfgN          ( ChimneyCfgN                   ),
            .ChimneyCfgW          ( ChimneyCfgW                   ),
            .AtopSupport          ( '0                            ),
            .RouteCfg             ( RouteCfg                      ),
            .id_t                 ( id_t                          ),
            .rob_idx_t            ( rob_idx_t                     ),
            .route_t              ( route_t                       ),
            .dst_t                ( route_t                       ),
            .hdr_t                ( hdr_t                         ),
            .sam_rule_t           ( sam_rule_t                    ),
            .Sam                  ( Sam                           ),
            .axi_narrow_in_req_t  ( axi_narrow_in_req_t           ),
            .axi_narrow_in_rsp_t  ( axi_narrow_in_rsp_t           ),
            .axi_narrow_out_req_t ( axi_narrow_out_req_t          ),
            .axi_narrow_out_rsp_t ( axi_narrow_out_rsp_t          ),
            .axi_wide_in_req_t    ( axi_wide_in_req_t             ),
            .axi_wide_in_rsp_t    ( axi_wide_in_rsp_t             ),
            .axi_wide_out_req_t   ( axi_wide_out_req_t            ),
            .axi_wide_out_rsp_t   ( axi_wide_out_rsp_t            ),
            .floo_req_t           ( floo_req_t                    ),
            .floo_rsp_t           ( floo_rsp_t                    ),
            .floo_wide_t          ( floo_wide_t                   )
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
            .axi_wide_out_req_o   ( axi_mst_req[x]                ),
            .axi_wide_out_rsp_i   ( axi_mst_resp[x]               ),
            .id_i                 ( id_t'(HbmNi0+x)               ),
            .route_table_i        ( RoutingTables[HbmNi0+x]       ),
            .floo_req_o           ( floo_axi_req_in[x]            ),
            .floo_rsp_o           ( floo_axi_rsp_in[x]            ),
            .floo_wide_o          ( floo_axi_wide_in[x]           ),
            .floo_req_i           ( floo_axi_req_out[x]           ),
            .floo_rsp_i           ( floo_axi_rsp_out[x]           ),
            .floo_wide_i          ( floo_axi_wide_out[x]          )
          );
      end
    end
     
  `else
    `define CLUSTER_WRAPPER mempool_cluster_floonoc_wrapper
    // AXI Chimney
    floo_req_t  [NumAXIMasters:0] floo_axi_req_in;
    floo_rsp_t  [NumAXIMasters:0] floo_axi_rsp_in;
    floo_wide_t [NumAXIMasters:0] floo_axi_wide_in;
    floo_req_t  [NumAXIMasters:0] floo_axi_req_out;
    floo_rsp_t  [NumAXIMasters:0] floo_axi_rsp_out;
    floo_wide_t [NumAXIMasters:0] floo_axi_wide_out;
    for (genvar x = 0; x <= NumAXIMasters; x++) begin : gen_cluster_axi_chimney
        if (x == NumAXIMasters) begin
          floo_req_t  [2:0] periph_router_req_in;
          floo_rsp_t  [2:0] periph_router_rsp_out;
          floo_req_t  [2:0] periph_router_req_out;
          floo_rsp_t  [2:0] periph_router_rsp_in;
          floo_wide_t [2:0] periph_router_wide_in;
          floo_wide_t [2:0] periph_router_wide_out;

          assign periph_router_req_in[0]  = floo_axi_req_out[x];
          assign periph_router_rsp_in[0]  = floo_axi_rsp_out[x];
          assign periph_router_wide_in[0] = floo_axi_wide_out[x];
          assign floo_axi_req_in[x]       = periph_router_req_out[0];
          assign floo_axi_rsp_in[x]       = periph_router_rsp_out[0];
          assign floo_axi_wide_in[x]      = periph_router_wide_out[0];

          floo_nw_router #(
            .AxiCfgN              ( AxiCfgN                       ),
            .AxiCfgW              ( AxiCfgW                       ),
            .RouteAlgo            ( RouteCfg.RouteAlgo            ),
            .NumRoutes            ( 3                             ),
            .InFifoDepth          ( 2                             ),
            .OutFifoDepth         ( 2                             ),
            .id_t                 ( id_t                          ),
            .hdr_t                ( hdr_t                         ),
            .floo_req_t           ( floo_req_t                    ),
            .floo_rsp_t           ( floo_rsp_t                    ),
            .floo_wide_t          ( floo_wide_t                   ),
            .NumAddrRules         (1                              )
          ) periph_router (
            .clk_i,
            .rst_ni,
            .test_enable_i        ( testmode_i                    ),
            .id_i                 ( '0                            ),
            .id_route_map_i       ( '0                            ),
            .floo_req_i           ( periph_router_req_in          ),
            .floo_rsp_o           ( periph_router_rsp_out         ),
            .floo_req_o           ( periph_router_req_out         ),
            .floo_rsp_i           ( periph_router_rsp_in          ),
            .floo_wide_i          ( periph_router_wide_in         ),
            .floo_wide_o          ( periph_router_wide_out        )
          );

          localparam floo_pkg::chimney_cfg_t PeriphChimneyCfgW = floo_pkg::set_ports(floo_pkg::ChimneyDefaultCfg, 1'b1, 1'b0);
          floo_nw_chimney #(
            .AxiCfgN              ( AxiCfgN                       ),
            .AxiCfgW              ( AxiCfgW                       ),
            .ChimneyCfgN          ( ChimneyCfgN                   ),
            .ChimneyCfgW          ( PeriphChimneyCfgW             ),
            .AtopSupport          ( '0                            ),
            .RouteCfg             ( RouteCfg                      ),
            .id_t                 ( id_t                          ),
            .rob_idx_t            ( rob_idx_t                     ),
            .route_t              ( route_t                       ),
            .dst_t                ( route_t                       ),
            .hdr_t                ( hdr_t                         ),
            .sam_rule_t           ( sam_rule_t                    ),
            .Sam                  ( Sam                           ),
            .axi_narrow_in_req_t  ( axi_narrow_in_req_t           ),
            .axi_narrow_in_rsp_t  ( axi_narrow_in_rsp_t           ),
            .axi_narrow_out_req_t ( axi_narrow_out_req_t          ),
            .axi_narrow_out_rsp_t ( axi_narrow_out_rsp_t          ),
            .axi_wide_in_req_t    ( axi_wide_in_req_t             ),
            .axi_wide_in_rsp_t    ( axi_wide_in_rsp_t             ),
            .axi_wide_out_req_t   ( axi_wide_out_req_t            ),
            .axi_wide_out_rsp_t   ( axi_wide_out_rsp_t            ),
            .floo_req_t           ( floo_req_t                    ),
            .floo_rsp_t           ( floo_rsp_t                    ),
            .floo_wide_t          ( floo_wide_t                   )
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
            .axi_wide_out_req_o   ( axi_mst_periph_req            ),
            .axi_wide_out_rsp_i   ( axi_mst_periph_resp           ),
            .id_i                 ( id_t'(PeripheralsNi)          ),
            .route_table_i        ( RoutingTables[PeripheralsNi]  ),
            .floo_req_o           ( periph_router_req_in[1]       ),
            .floo_rsp_i           ( periph_router_rsp_out[1]      ),
            .floo_wide_o          ( periph_router_wide_in[1]      ),
            .floo_req_i           ( periph_router_req_out[1]      ),
            .floo_rsp_o           ( periph_router_rsp_in[1]       ),
            .floo_wide_i          ( periph_router_wide_out[1]     )
          );

          localparam floo_pkg::chimney_cfg_t HostChimneyCfgW = floo_pkg::set_ports(floo_pkg::ChimneyDefaultCfg, 1'b0, 1'b1);
          floo_nw_chimney #(
            .AxiCfgN              ( AxiCfgN                       ),
            .AxiCfgW              ( AxiCfgW                       ),
            .ChimneyCfgN          ( ChimneyCfgN                   ),
            .ChimneyCfgW          ( HostChimneyCfgW               ),
            .RouteCfg             ( RouteCfg                      ),
            .id_t                 ( id_t                          ),
            .rob_idx_t            ( rob_idx_t                     ),
            .route_t              ( route_t                       ),
            .dst_t                ( route_t                       ),
            .hdr_t                ( hdr_t                         ),
            .sam_rule_t           ( sam_rule_t                    ),
            .Sam                  ( Sam                           ),
            .axi_narrow_in_req_t  ( axi_narrow_in_req_t           ),
            .axi_narrow_in_rsp_t  ( axi_narrow_in_rsp_t           ),
            .axi_narrow_out_req_t ( axi_narrow_out_req_t          ),
            .axi_narrow_out_rsp_t ( axi_narrow_out_rsp_t          ),
            .axi_wide_in_req_t    ( axi_wide_in_req_t             ),
            .axi_wide_in_rsp_t    ( axi_wide_in_rsp_t             ),
            .axi_wide_out_req_t   ( axi_wide_out_req_t            ),
            .axi_wide_out_rsp_t   ( axi_wide_out_rsp_t            ),
            .floo_req_t           ( floo_req_t                    ),
            .floo_rsp_t           ( floo_rsp_t                    ),
            .floo_wide_t          ( floo_wide_t                   )
          ) host_ni (
            .clk_i,
            .rst_ni,
            .test_enable_i        ( testmode_i                    ),
            .sram_cfg_i           ( '0                            ),
            .axi_narrow_in_req_i  ( '0                            ),
            .axi_narrow_in_rsp_o  (                               ),
            .axi_narrow_out_req_o (                               ),
            .axi_narrow_out_rsp_i ( '0                            ),
            .axi_wide_in_req_i    ( slv_req_i                     ),
            .axi_wide_in_rsp_o    ( slv_resp_o                    ),
            .axi_wide_out_req_o   (                               ),
            .axi_wide_out_rsp_i   ( '0                            ),
            .id_i                 ( id_t'(HostNi)                 ),
            .route_table_i        ( RoutingTables[HostNi]         ),
            .floo_req_o           ( periph_router_req_in[2]       ),
            .floo_rsp_i           ( periph_router_rsp_out[2]      ),
            .floo_wide_o          ( periph_router_wide_in[2]      ),
            .floo_req_i           ( periph_router_req_out[2]      ),
            .floo_rsp_o           ( periph_router_rsp_in[2]       ),
            .floo_wide_i          ( periph_router_wide_out[2]     )
          );
        end else begin
          floo_nw_chimney #(
            .AxiCfgN              ( AxiCfgN                       ),
            .AxiCfgW              ( AxiCfgW                       ),
            .ChimneyCfgN          ( ChimneyCfgN                   ),
            .ChimneyCfgW          ( ChimneyCfgW                   ),
            .AtopSupport          ( '0                            ),
            .RouteCfg             ( RouteCfg                      ),
            .id_t                 ( id_t                          ),
            .rob_idx_t            ( rob_idx_t                     ),
            .route_t              ( route_t                       ),
            .dst_t                ( route_t                       ),
            .hdr_t                ( hdr_t                         ),
            .sam_rule_t           ( sam_rule_t                    ),
            .Sam                  ( Sam                           ),
            .axi_narrow_in_req_t  ( axi_narrow_in_req_t           ),
            .axi_narrow_in_rsp_t  ( axi_narrow_in_rsp_t           ),
            .axi_narrow_out_req_t ( axi_narrow_out_req_t          ),
            .axi_narrow_out_rsp_t ( axi_narrow_out_rsp_t          ),
            .axi_wide_in_req_t    ( axi_wide_in_req_t             ),
            .axi_wide_in_rsp_t    ( axi_wide_in_rsp_t             ),
            .axi_wide_out_req_t   ( axi_wide_out_req_t            ),
            .axi_wide_out_rsp_t   ( axi_wide_out_rsp_t            ),
            .floo_req_t           ( floo_req_t                    ),
            .floo_rsp_t           ( floo_rsp_t                    ),
            .floo_wide_t          ( floo_wide_t                   )
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
            .axi_wide_out_req_o   ( axi_mst_req[x]                ),
            .axi_wide_out_rsp_i   ( axi_mst_resp[x]               ),
            .id_i                 ( id_t'(HbmNi0+x)               ),
            .route_table_i        ( RoutingTables[HbmNi0+x]       ),
            .floo_req_o           ( floo_axi_req_in[x]            ),
            .floo_rsp_o           ( floo_axi_rsp_in[x]            ),
            .floo_wide_o          ( floo_axi_wide_in[x]           ),
            .floo_req_i           ( floo_axi_req_out[x]           ),
            .floo_rsp_i           ( floo_axi_rsp_out[x]           ),
            .floo_wide_i          ( floo_axi_wide_out[x]          )
          );
      end
    end
  `endif

  `CLUSTER_WRAPPER #(
    .TCDMBaseAddr(TCDMBaseAddr),
    .BootAddr    (BootAddr)
  ) i_mempool_cluster (
    .clk_i             (clk_i),
    .rst_ni            (rst_ni),
    .wake_up_i         (wake_up),
    .testmode_i        (1'b0),
    .scan_enable_i     (1'b0),
    .scan_data_i       (1'b0),
    .scan_data_o       (/* Unused */),
    .ro_cache_ctrl_i   (ro_cache_ctrl),
    .dma_req_i         (dma_group_req),
    .dma_req_valid_i   (dma_group_req_valid),
    .dma_req_ready_o   (dma_group_req_ready),
    .dma_meta_o        (dma_group_meta),
    .floo_axi_req_i    (floo_axi_req_in),
    .floo_axi_rsp_i    (floo_axi_rsp_in),
    .floo_axi_wide_i   (floo_axi_wide_in),
    .floo_axi_req_o    (floo_axi_req_out),
    .floo_axi_rsp_o    (floo_axi_rsp_out),
    .floo_axi_wide_o   (floo_axi_wide_out)
  );

  /**********************
   *  AXI Interconnect  *
   **********************/

  localparam addr_t PeripheralsBaseAddr   = 32'h4000_0000;
  localparam addr_t PeripheralsEndAddr    = 32'h4002_0000;
  localparam addr_t L2MemoryBaseAddr      = `ifdef L2_BASE `L2_BASE `else 32'h8000_0000 `endif;
  localparam addr_t L2MemoryEndAddr       = L2MemoryBaseAddr + L2Size;
  localparam addr_t BootromBaseAddr       = 32'hA000_0000;
  localparam addr_t BootromEndAddr        = 32'hA000_FFFF;

  assign axi_l2_req          = axi_mst_req;
  assign axi_mst_resp        = axi_l2_resp;
  assign axi_soc_req         = axi_mst_periph_req;
  assign axi_mst_periph_resp = axi_soc_resp;

  xbar_rule_32_t [NumSoCRules-1:0]  soc_xbar_rules;

  assign soc_xbar_rules = '{
    '{idx: Peripherals, start_addr: PeripheralsBaseAddr, end_addr: PeripheralsEndAddr},
    '{idx: Bootrom, start_addr: BootromBaseAddr, end_addr: BootromEndAddr}
  };

  axi_xbar #(
    .Cfg          (SoCXBarCfg       ),
    .slv_aw_chan_t(axi_tile_aw_t    ),
    .mst_aw_chan_t(axi_system_aw_t  ),
    .w_chan_t     (axi_tile_w_t     ),
    .slv_b_chan_t (axi_tile_b_t     ),
    .mst_b_chan_t (axi_system_b_t   ),
    .slv_ar_chan_t(axi_tile_ar_t    ),
    .mst_ar_chan_t(axi_system_ar_t  ),
    .slv_r_chan_t (axi_tile_r_t     ),
    .mst_r_chan_t (axi_system_r_t   ),
    .slv_req_t    (axi_tile_req_t   ),
    .slv_resp_t   (axi_tile_resp_t  ),
    .mst_req_t    (axi_system_req_t ),
    .mst_resp_t   (axi_system_resp_t),
    .rule_t       (xbar_rule_32_t   )
  ) i_soc_xbar (
    .clk_i                (clk_i                    ),
    .rst_ni               (rst_ni                   ),
    .test_i               (1'b0                     ),
    .slv_ports_req_i      (axi_soc_req              ),
    .slv_ports_resp_o     (axi_soc_resp             ),
    .mst_ports_req_o      (axi_periph_req           ),
    .mst_ports_resp_i     (axi_periph_resp          ),
    .addr_map_i           (soc_xbar_rules           ),
    .en_default_mst_port_i('1                       ), // default all slave ports to master port External
    .default_mst_port_i   (External                 )
  );

`ifndef DRAM

  /*************
   *  L2 SRAM  *
   *************/

  localparam int unsigned NumAXIMastersLog2 = NumAXIMasters == 1 ? 1 : $clog2(NumAXIMasters);
  typedef logic [L2AddrWidth-1:0] l2_mem_addr_t;
  typedef logic [L2BankAddrWidth-1:0] l2_bank_addr_t;
  typedef logic [NumAXIMastersLog2-1:0] bank_ini_t;
  // Axi2Mems to l2_xbar
  logic         [NumAXIMasters-1:0] mem_req;
  logic         [NumAXIMasters-1:0] mem_gnt;
  logic         [NumAXIMasters-1:0] mem_rvalid;
  addr_t        [NumAXIMasters-1:0] mem_addr_full;
  l2_mem_addr_t [NumAXIMasters-1:0] mem_addr;
  axi_data_t    [NumAXIMasters-1:0] mem_wdata;
  axi_strb_t    [NumAXIMasters-1:0] mem_strb;
  logic         [NumAXIMasters-1:0] mem_we;
  axi_data_t    [NumAXIMasters-1:0] mem_rdata;
  // l2_xbar to banks
  logic          [NumL2Banks-1:0] bank_req;
  logic          [NumL2Banks-1:0] bank_gnt;
  logic          [NumL2Banks-1:0] bank_rvalid;
  l2_bank_addr_t [NumL2Banks-1:0] bank_addr;
  axi_data_t     [NumL2Banks-1:0] bank_wdata;
  axi_strb_t     [NumL2Banks-1:0] bank_strb;
  logic          [NumL2Banks-1:0] bank_we;
  axi_data_t     [NumL2Banks-1:0] bank_rdata;

  for (genvar i = 0; i < NumAXIMasters; i++) begin : gen_l2_adapters
    axi2mem #(
      .axi_req_t (axi_tile_req_t ),
      .axi_resp_t(axi_tile_resp_t),
      .AddrWidth (L2AddrWidth    ),
      .DataWidth (AxiDataWidth   ),
      .IdWidth   (AxiTileIdWidth ),
      .NumBanks  (1              ),
      .BufDepth  (3              )
    ) i_axi2mem (
      .clk_i       (clk_i         ),
      .rst_ni      (rst_ni        ),
      .busy_o      (/*unsused*/   ),
      .axi_req_i   (axi_l2_req[i] ),
      .axi_resp_o  (axi_l2_resp[i]),
      .mem_req_o   (mem_req[i]    ),
      .mem_gnt_i   (mem_gnt[i]    ),
      .mem_addr_o  (mem_addr[i]   ),
      .mem_wdata_o (mem_wdata[i]  ),
      .mem_strb_o  (mem_strb[i]   ),
      .mem_atop_o  (/*unused*/    ),
      .mem_we_o    (mem_we[i]     ),
      .mem_rvalid_i(mem_rvalid[i] ),
      .mem_rdata_i (mem_rdata[i]  )
    );

    assign bank_req[i]    = mem_req[i];
    assign mem_gnt[i]     = '1;
    assign bank_addr[i]   = mem_addr[i][$clog2(L2BankBeWidth-1) +: L2BankAddrWidth];
    assign bank_we[i]     = mem_we[i];
    assign bank_wdata[i]  = mem_wdata[i];
    assign bank_strb[i]   = mem_strb[i];
    assign mem_rvalid[i]  = bank_rvalid[i];
    assign mem_rdata[i]   = bank_rdata[i];
  end

  `FF(bank_rvalid, bank_req, 1'b0, clk_i, rst_ni)

  // The initialization at reset is not supported by Verilator. Therefore, we disable the SimInit at
  // reset for Verilator. Since our preloading through the SystemVerilog testbench requires the
  // SimInit value to be assigned at reset, we use the "custom" string to invoke the initialization
  // without setting the memory to known values like "ones" or "zeros".
  localparam L2SimInit = `ifdef VERILATOR "none" `else "custom" `endif;
  for (genvar i = 0; i < NumL2Banks; i++) begin : gen_l2_banks
    tc_sram #(
      .DataWidth(L2BankWidth   ),
      .NumWords (L2BankNumWords),
      .NumPorts (1             ),
      .SimInit  (L2SimInit     )
    ) l2_mem (
      .clk_i  (clk_i        ),
      .rst_ni (rst_ni       ),
      .req_i  (bank_req[i]  ),
      .we_i   (bank_we[i]   ),
      .addr_i (bank_addr[i] ),
      .wdata_i(bank_wdata[i]),
      .be_i   (bank_strb[i] ),
      .rdata_o(bank_rdata[i])
    );
  end

`else

  /*************
   *  L2 DRAM  *
   *************/

  axi_tile_req_t  [NumDrams-1:0] dram_req;
  axi_tile_resp_t [NumDrams-1:0] dram_resp;

  // Local parameters for address manipulation
  localparam int unsigned LSBConstantBits = $clog2(L2BankBeWidth * Interleave);
  localparam int unsigned MSBConstantBits = 32 - $clog2(L2Size);
  localparam int unsigned ScrambleBits    = (NumDrams == 1) ? 1 : $clog2(NumDrams);
  localparam int unsigned ReminderBits    = AddrWidth - ScrambleBits - LSBConstantBits - MSBConstantBits;

  // Logic variables for address scrambling reset
  logic [NumAXIMasters-1:0][LSBConstantBits-1:0] aw_lsb_const;
  logic [NumAXIMasters-1:0][MSBConstantBits-1:0] aw_msb_const;
  logic [NumAXIMasters-1:0][ScrambleBits-1:0   ] aw_scramble;
  logic [NumAXIMasters-1:0][ReminderBits-1:0   ] aw_reminder;
  logic [NumAXIMasters-1:0][AddrWidth-1:0      ] aw_scramble_reset_addr;

  logic [NumAXIMasters-1:0][LSBConstantBits-1:0] ar_lsb_const;
  logic [NumAXIMasters-1:0][MSBConstantBits-1:0] ar_msb_const;
  logic [NumAXIMasters-1:0][ScrambleBits-1:0   ] ar_scramble;
  logic [NumAXIMasters-1:0][ReminderBits-1:0   ] ar_reminder;
  logic [NumAXIMasters-1:0][AddrWidth-1:0      ] ar_scramble_reset_addr;

  // Address scrambling reset logic
  for (genvar i = 0; i < NumAXIMasters; i++) begin : addr_scrambler_reset
    always_comb begin
      dram_req[i]    = axi_l2_req[i];
      axi_l2_resp[i] = dram_resp[i];
      // AW Channel
      // Decompose address for scrambling
      aw_lsb_const[i]           = dram_req[i].aw.addr[LSBConstantBits-1 : 0];
      aw_msb_const[i]           = dram_req[i].aw.addr[AddrWidth-1 -: MSBConstantBits] - L2MemoryBaseAddr[AddrWidth-1-: MSBConstantBits];
      aw_scramble[i]            = dram_req[i].aw.addr[AddrWidth-MSBConstantBits-1 -: ScrambleBits];
      aw_reminder[i]            = dram_req[i].aw.addr[AddrWidth-MSBConstantBits-ScrambleBits-1 : LSBConstantBits];
      aw_scramble_reset_addr[i] = {{ScrambleBits{1'b0}}, aw_msb_const[i], aw_reminder[i], aw_lsb_const[i]};
      // Assign scrambled address back to request
      dram_req[i].aw.addr       = aw_scramble_reset_addr[i];

      // AR Channel
      // Decompose address for scrambling
      ar_lsb_const[i]           = dram_req[i].ar.addr[LSBConstantBits-1 : 0];
      ar_msb_const[i]           = dram_req[i].ar.addr[AddrWidth-1 -: MSBConstantBits] - L2MemoryBaseAddr[AddrWidth-1-: MSBConstantBits];
      ar_scramble[i]            = dram_req[i].ar.addr[AddrWidth-MSBConstantBits-1 -: ScrambleBits];
      ar_reminder[i]            = dram_req[i].ar.addr[AddrWidth-MSBConstantBits-ScrambleBits-1 : LSBConstantBits];
      ar_scramble_reset_addr[i] = {{ScrambleBits{1'b0}}, ar_msb_const[i], ar_reminder[i], ar_lsb_const[i]};
      // Assign scrambled address back to request
      dram_req[i].ar.addr       = ar_scramble_reset_addr[i];
    end
  end

  for (genvar i = 0; unsigned'(i) < NumDrams; i++) begin: gen_drams
    axi_dram_sim #(
        .AxiAddrWidth(AddrWidth        ),
        .AxiDataWidth(AxiDataWidth     ),
        .AxiIdWidth  (AxiTileIdWidth   ),
        .AxiUserWidth(1                ),
        .DRAMType    ("HBM2"           ),
        .BASE        ('b0              ),
        .axi_req_t   (axi_tile_req_t   ),
        .axi_resp_t  (axi_tile_resp_t  ),
        .axi_ar_t    (axi_tile_ar_t    ),
        .axi_r_t     (axi_tile_r_t     ),
        .axi_aw_t    (axi_tile_aw_t    ),
        .axi_w_t     (axi_tile_w_t     ),
        .axi_b_t     (axi_tile_b_t     )
    ) i_axi_dram_sim (
        .clk_i,
        .rst_ni,
        .axi_req_i (dram_req[i] ),
        .axi_resp_o(dram_resp[i])
    );
  end: gen_drams
`endif

  /*************
   *  Bootrom  *
   *************/

  // Memory
  logic      bootrom_req;
  logic      bootrom_rvalid;
  addr_t     bootrom_addr;
  axi_data_t bootrom_rdata;

  axi2mem #(
    .axi_req_t  (axi_system_req_t ),
    .axi_resp_t (axi_system_resp_t),
    .AddrWidth  (AddrWidth        ),
    .DataWidth  (AxiDataWidth     ),
    .IdWidth    (AxiSystemIdWidth ),
    .NumBanks   (1                ),
    .BufDepth   (2                )
  ) i_axi2mem_bootrom (
    .clk_i        (clk_i                   ),
    .rst_ni       (rst_ni                  ),
    .busy_o       (/*unsused*/             ),
    .axi_req_i    (axi_periph_req[Bootrom] ),
    .axi_resp_o   (axi_periph_resp[Bootrom]),
    .mem_req_o    (bootrom_req             ),
    .mem_gnt_i    (bootrom_req             ),
    .mem_addr_o   (bootrom_addr            ),
    .mem_wdata_o  (/*unused*/              ),
    .mem_strb_o   (/*unused*/              ),
    .mem_atop_o   (/*unused*/              ),
    .mem_we_o     (/*unused*/              ),
    .mem_rvalid_i (bootrom_rvalid          ),
    .mem_rdata_i  (bootrom_rdata           )
  );

  `FF(bootrom_rvalid, bootrom_req, 1'b0, clk_i, rst_ni)

  bootrom i_bootrom (
    .clk_i  (clk_i        ),
    .req_i  (bootrom_req  ),
    .addr_i (bootrom_addr ),
    .rdata_o(bootrom_rdata)
  );

  /***********************
   *  Control Registers  *
   ***********************/

  localparam NumPeriphs = 2; // Control registers + DMA

  typedef enum logic [$clog2(NumPeriphs) - 1:0] {
    CtrlRegisters,
    DMA
  } axi_lite_xbar_slave_target;

  axi_periph_req_t                     axi_periph_narrow_req;
  axi_periph_resp_t                    axi_periph_narrow_resp;
  axi_lite_slv_req_t                   axi_lite_mst_req;
  axi_lite_slv_resp_t                  axi_lite_mst_resp;
  axi_lite_slv_req_t  [NumPeriphs-1:0] axi_lite_slv_req;
  axi_lite_slv_resp_t [NumPeriphs-1:0] axi_lite_slv_resp;

  localparam xbar_cfg_t AXILiteXBarCfg = '{
    NoSlvPorts         : 1,
    NoMstPorts         : NumPeriphs,
    MaxMstTrans        : 1,
    MaxSlvTrans        : 1,
    FallThrough        : 1'b0,
    LatencyMode        : axi_pkg::NO_LATENCY,
    PipelineStages     : 0,
    AxiIdWidthSlvPorts : 0, /* Not used for AXI lite */
    AxiIdUsedSlvPorts  : 0, /* Not used for AXI lite */
    UniqueIds          : 0, /* Not used for AXI lite */
    AxiAddrWidth       : AddrWidth,
    AxiDataWidth       : AxiLiteDataWidth,
    NoAddrRules        : NumPeriphs
  };

  localparam addr_t CtrlRegistersBaseAddr = 32'h4000_0000;
  localparam addr_t CtrlRegistersEndAddr  = 32'h4001_0000;
  localparam addr_t DMABaseAddr           = 32'h4001_0000;
  localparam addr_t DMAEndAddr            = 32'h4002_0000;

  xbar_rule_32_t [NumPeriphs-1:0] axi_lite_xbar_rules;
  assign axi_lite_xbar_rules = '{
    '{idx: CtrlRegisters, start_addr: CtrlRegistersBaseAddr, end_addr: CtrlRegistersEndAddr},
    '{idx: DMA, start_addr: DMABaseAddr, end_addr: DMAEndAddr}
  };

  axi_dw_converter #(
    .AxiMaxReads         (1                ), // Number of outstanding reads
    .AxiSlvPortDataWidth (AxiDataWidth     ), // Data width of the slv port
    .AxiMstPortDataWidth (AxiLiteDataWidth ), // Data width of the mst port
    .AxiAddrWidth        (AddrWidth        ), // Address width
    .AxiIdWidth          (AxiSystemIdWidth ), // ID width
    .aw_chan_t           (axi_system_aw_t  ), // AW Channel Type
    .mst_w_chan_t        (axi_periph_w_t   ), //  W Channel Type for the mst port
    .slv_w_chan_t        (axi_system_w_t   ), //  W Channel Type for the slv port
    .b_chan_t            (axi_system_b_t   ), //  B Channel Type
    .ar_chan_t           (axi_system_ar_t  ), // AR Channel Type
    .mst_r_chan_t        (axi_periph_r_t   ), //  R Channel Type for the mst port
    .slv_r_chan_t        (axi_system_r_t   ), //  R Channel Type for the slv port
    .axi_mst_req_t       (axi_periph_req_t ), // AXI Request Type for mst ports
    .axi_mst_resp_t      (axi_periph_resp_t), // AXI Response Type for mst ports
    .axi_slv_req_t       (axi_system_req_t ), // AXI Request Type for slv ports
    .axi_slv_resp_t      (axi_system_resp_t)  // AXI Response Type for slv ports
  ) i_axi_dw_converter_ctrl (
    .clk_i      (clk_i                       ),
    .rst_ni     (rst_ni                      ),
    // Slave interface
    .slv_req_i  (axi_periph_req[Peripherals] ),
    .slv_resp_o (axi_periph_resp[Peripherals]),
    // Master interface
    .mst_req_o  (axi_periph_narrow_req       ),
    .mst_resp_i (axi_periph_narrow_resp      )
  );

  axi_to_axi_lite #(
    .AxiAddrWidth   (AddrWidth          ),
    .AxiDataWidth   (AxiLiteDataWidth   ),
    .AxiIdWidth     (AxiSystemIdWidth   ),
    .AxiUserWidth   (1                  ),
    .AxiMaxReadTxns (1                  ),
    .AxiMaxWriteTxns(1                  ),
    .FallThrough    (1'b0               ),
    .full_req_t     (axi_periph_req_t   ),
    .full_resp_t    (axi_periph_resp_t  ),
    .lite_req_t     (axi_lite_slv_req_t ),
    .lite_resp_t    (axi_lite_slv_resp_t)
  ) i_axi_to_axi_lite (
    .clk_i     (clk_i                 ),
    .rst_ni    (rst_ni                ),
    .test_i    (1'b0                  ),
    .slv_req_i (axi_periph_narrow_req ),
    .slv_resp_o(axi_periph_narrow_resp),
    .mst_req_o (axi_lite_mst_req      ),
    .mst_resp_i(axi_lite_mst_resp     )
  );

  axi_lite_xbar #(
    .Cfg       (AXILiteXBarCfg     ),
    .aw_chan_t (axi_lite_slv_aw_t  ),
    .w_chan_t  (axi_lite_slv_w_t   ),
    .b_chan_t  (axi_lite_slv_b_t   ),
    .ar_chan_t (axi_lite_slv_ar_t  ),
    .r_chan_t  (axi_lite_slv_r_t   ),
    .axi_req_t (axi_lite_slv_req_t ),
    .axi_resp_t(axi_lite_slv_resp_t),
    .rule_t    (xbar_rule_32_t     )
  ) i_axi_lite_xbar (
    .clk_i                (clk_i              ),
    .rst_ni               (rst_ni             ),
    .test_i               (1'b0               ),
    .slv_ports_req_i      (axi_lite_mst_req   ),
    .slv_ports_resp_o     (axi_lite_mst_resp  ),
    .mst_ports_req_o      (axi_lite_slv_req   ),
    .mst_ports_resp_i     (axi_lite_slv_resp  ),
    .addr_map_i           (axi_lite_xbar_rules),
    .en_default_mst_port_i('1                 ),
    .default_mst_port_i   (CtrlRegisters      )
  );

  ctrl_registers #(
    .NumRegs          (16 + 16            ),
    .TCDMBaseAddr     (TCDMBaseAddr       ),
    .TCDMSize         (TCDMSize           ),
    .NumCores         (NumCores           ),
    .axi_lite_req_t (axi_lite_slv_req_t ),
    .axi_lite_resp_t(axi_lite_slv_resp_t)
  ) i_ctrl_registers (
    .clk_i                (clk_i                           ),
    .rst_ni               (rst_ni                          ),
    .axi_lite_slave_req_i (axi_lite_slv_req[CtrlRegisters] ),
    .axi_lite_slave_resp_o(axi_lite_slv_resp[CtrlRegisters]),
    .ro_cache_ctrl_o      (ro_cache_ctrl                   ),
    .tcdm_start_address_o (/* Unused */                    ),
    .tcdm_end_address_o   (/* Unused */                    ),
    .num_cores_o          (/* Unused */                    ),
    .wake_up_o            (wake_up                         ),
    .eoc_o                (/* Unused */                    ),
    .eoc_valid_o          (eoc_valid_o                     )
  );

  /***************************
   *  DMA Midend + Frontend  *
   ***************************/

  dma_req_t          dma_req;
  logic              dma_req_valid;
  logic              dma_req_ready;
  dma_meta_t         dma_meta;
  logic      [1-1:0] dma_id;

  mempool_dma #(
    .axi_lite_req_t(axi_lite_slv_req_t       ),
    .axi_lite_rsp_t(axi_lite_slv_resp_t      ),
    .burst_req_t   (dma_req_t                ),
    .NumBackends   (NumGroups                ),
    .DmaIdWidth    (1                        )
  ) i_mempool_dma (
    .clk_i           (clk_i                  ),
    .rst_ni          (rst_ni                 ),
    .config_req_i    (axi_lite_slv_req[DMA]  ),
    .config_res_o    (axi_lite_slv_resp[DMA] ),
    .burst_req_o     (dma_req                ),
    .valid_o         (dma_req_valid          ),
    .ready_i         (dma_req_ready          ),
    .backend_idle_i  (dma_meta.backend_idle  ),
    .trans_complete_i(dma_meta.trans_complete),
    .dma_id_o        (dma_id                 )
  );

  dma_req_t  dma_req_cut;
  logic      dma_req_cut_valid;
  logic      dma_req_cut_ready;
  dma_meta_t dma_meta_cut;

  `FF(dma_meta, dma_meta_cut, '0, clk_i, rst_ni);
  
  spill_register #(
    .T(dma_req_t)
  ) i_dma_req_register (
    .clk_i  (clk_i            ),
    .rst_ni (rst_ni           ),
    .data_i (dma_req          ),
    .valid_i(dma_req_valid    ),
    .ready_o(dma_req_ready    ),
    .data_o (dma_req_cut      ),
    .valid_o(dma_req_cut_valid),
    .ready_i(dma_req_cut_ready)
  );

  dma_req_t  dma_req_split;
  logic      dma_req_split_valid;
  logic      dma_req_split_ready;
  dma_meta_t dma_meta_split;

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
    .burst_req_o (dma_group_req      ),
    .valid_o     (dma_group_req_valid),
    .ready_i     (dma_group_req_ready),
    .meta_i      (dma_group_meta     )
  );

  assign busy_o = 1'b0;

  // From MemPool to the Host
  assign mst_req_o                 = axi_periph_req[External];
  assign axi_periph_resp[External] = mst_resp_i;

endmodule : mempool_system
