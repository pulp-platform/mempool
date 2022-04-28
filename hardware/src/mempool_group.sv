// Copyright 2021 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "mempool/mempool.svh"

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
  output `STRUCT_VECT(tcdm_slave_req_t,   [NumGroups-1:1][NumTilesPerGroup-1:0]) tcdm_master_req_o,
  output logic                            [NumGroups-1:1][NumTilesPerGroup-1:0]  tcdm_master_req_valid_o,
  input  logic                            [NumGroups-1:1][NumTilesPerGroup-1:0]  tcdm_master_req_ready_i,
  input  `STRUCT_VECT(tcdm_master_resp_t, [NumGroups-1:1][NumTilesPerGroup-1:0]) tcdm_master_resp_i,
  input  logic                            [NumGroups-1:1][NumTilesPerGroup-1:0]  tcdm_master_resp_valid_i,
  output logic                            [NumGroups-1:1][NumTilesPerGroup-1:0]  tcdm_master_resp_ready_o,
  // TCDM Slave interfaces
  input  `STRUCT_VECT(tcdm_slave_req_t,   [NumGroups-1:1][NumTilesPerGroup-1:0]) tcdm_slave_req_i,
  input  logic                            [NumGroups-1:1][NumTilesPerGroup-1:0]  tcdm_slave_req_valid_i,
  output logic                            [NumGroups-1:1][NumTilesPerGroup-1:0]  tcdm_slave_req_ready_o,
  output `STRUCT_VECT(tcdm_master_resp_t, [NumGroups-1:1][NumTilesPerGroup-1:0]) tcdm_slave_resp_o,
  output logic                            [NumGroups-1:1][NumTilesPerGroup-1:0]  tcdm_slave_resp_valid_o,
  input  logic                            [NumGroups-1:1][NumTilesPerGroup-1:0]  tcdm_slave_resp_ready_i,
  // Wake up interface
  input  logic                            [NumCoresPerGroup-1:0]                 wake_up_i,
  // RO-Cache configuration
  input  `STRUCT_PORT(ro_cache_ctrl_t)                                           ro_cache_ctrl_i,
  // DMA request
  input  `STRUCT_VECT(dma_req_t,          [NumDMAsPerGroup-1:0])                 dma_req_i,
  input  logic                            [NumDMAsPerGroup-1:0]                  dma_req_valid_i,
  output logic                            [NumDMAsPerGroup-1:0]                  dma_req_ready_o,
   // AXI Interface
  output `STRUCT_VECT(axi_tile_req_t,     [NumAXIMastersPerGroup-1:0])           axi_mst_req_o,
  input  `STRUCT_VECT(axi_tile_resp_t,    [NumAXIMastersPerGroup-1:0])           axi_mst_resp_i
);

  /*****************
   *  Definitions  *
   *****************/

  typedef logic [idx_width(NumTiles)-1:0] tile_id_t;

  /**********************
   *  Ports to structs  *
   **********************/

  // The ports might be structs flattened to vectors. To access the structs'
  // internal signals, assign the flattened vectors back to structs.
  tcdm_slave_req_t   [NumGroups-1:1][NumTilesPerGroup-1:0] tcdm_master_req_s;
  tcdm_master_resp_t [NumGroups-1:1][NumTilesPerGroup-1:0] tcdm_slave_resp_s;

  for (genvar r = 1; r < NumGroups; r++) begin: gen_tcdm_struct
    assign tcdm_master_req_o[r] = tcdm_master_req_s[r];
    assign tcdm_slave_resp_o[r] = tcdm_slave_resp_s[r];
  end: gen_tcdm_struct

  /***********
   *  Tiles  *
   ***********/

  // TCDM interfaces
  tcdm_master_req_t  [NumGroups-1:0][NumTilesPerGroup-1:0] tcdm_master_req;
  logic              [NumGroups-1:0][NumTilesPerGroup-1:0] tcdm_master_req_valid;
  logic              [NumGroups-1:0][NumTilesPerGroup-1:0] tcdm_master_req_ready;
  tcdm_slave_req_t   [NumGroups-1:0][NumTilesPerGroup-1:0] tcdm_slave_req;
  logic              [NumGroups-1:0][NumTilesPerGroup-1:0] tcdm_slave_req_valid;
  logic              [NumGroups-1:0][NumTilesPerGroup-1:0] tcdm_slave_req_ready;
  tcdm_master_resp_t [NumGroups-1:0][NumTilesPerGroup-1:0] tcdm_master_resp;
  logic              [NumGroups-1:0][NumTilesPerGroup-1:0] tcdm_master_resp_valid;
  logic              [NumGroups-1:0][NumTilesPerGroup-1:0] tcdm_master_resp_ready;
  tcdm_slave_resp_t  [NumGroups-1:0][NumTilesPerGroup-1:0] tcdm_slave_resp;
  logic              [NumGroups-1:0][NumTilesPerGroup-1:0] tcdm_slave_resp_valid;
  logic              [NumGroups-1:0][NumTilesPerGroup-1:0] tcdm_slave_resp_ready;
  // DMA interfaces
  tcdm_slave_req_t   [NumTilesPerGroup-1:0][NumDMAPortsPerTile-1:0] tcdm_dma_req;
  logic              [NumTilesPerGroup-1:0][NumDMAPortsPerTile-1:0] tcdm_dma_req_valid;
  logic              [NumTilesPerGroup-1:0][NumDMAPortsPerTile-1:0] tcdm_dma_req_ready;
  tcdm_slave_resp_t  [NumTilesPerGroup-1:0][NumDMAPortsPerTile-1:0] tcdm_dma_resp;
  logic              [NumTilesPerGroup-1:0][NumDMAPortsPerTile-1:0] tcdm_dma_resp_valid;
  logic              [NumTilesPerGroup-1:0][NumDMAPortsPerTile-1:0] tcdm_dma_resp_ready;

  // Connect the IOs to the tiles' signals
  assign tcdm_master_resp[NumGroups-1:1]         = tcdm_master_resp_i[NumGroups-1:1];
  assign tcdm_master_resp_valid[NumGroups-1:1]   = tcdm_master_resp_valid_i[NumGroups-1:1];
  assign tcdm_master_resp_ready_o[NumGroups-1:1] = tcdm_master_resp_ready[NumGroups-1:1];
  assign tcdm_slave_req[NumGroups-1:1]           = tcdm_slave_req_i[NumGroups-1:1];
  assign tcdm_slave_req_valid[NumGroups-1:1]     = tcdm_slave_req_valid_i[NumGroups-1:1];
  assign tcdm_slave_req_ready_o[NumGroups-1:1]   = tcdm_slave_req_ready[NumGroups-1:1];

  // AXI interfaces
  axi_tile_req_t  [NumTilesPerGroup+NumDMAsPerGroup-1:0] axi_tile_req;
  axi_tile_resp_t [NumTilesPerGroup+NumDMAsPerGroup-1:0] axi_tile_resp;

  for (genvar t = 0; unsigned'(t) < NumTilesPerGroup; t++) begin: gen_tiles
    tile_id_t id;
    assign id = (group_id_i << $clog2(NumTilesPerGroup)) | t[idx_width(NumTilesPerGroup)-1:0];

    tcdm_master_req_t  [NumGroups-1:0] tran_tcdm_master_req;
    logic              [NumGroups-1:0] tran_tcdm_master_req_valid;
    logic              [NumGroups-1:0] tran_tcdm_master_req_ready;
    tcdm_slave_req_t   [NumGroups-1:0] tran_tcdm_slave_req;
    logic              [NumGroups-1:0] tran_tcdm_slave_req_valid;
    logic              [NumGroups-1:0] tran_tcdm_slave_req_ready;
    tcdm_master_resp_t [NumGroups-1:0] tran_tcdm_master_resp;
    logic              [NumGroups-1:0] tran_tcdm_master_resp_valid;
    logic              [NumGroups-1:0] tran_tcdm_master_resp_ready;
    tcdm_slave_resp_t  [NumGroups-1:0] tran_tcdm_slave_resp;
    logic              [NumGroups-1:0] tran_tcdm_slave_resp_valid;
    logic              [NumGroups-1:0] tran_tcdm_slave_resp_ready;

    mempool_tile #(
      .TCDMBaseAddr(TCDMBaseAddr),
      .BootAddr    (BootAddr    )
    ) i_tile (
      .clk_i                   (clk_i                                          ),
      .rst_ni                  (rst_ni                                         ),
      .scan_enable_i           (scan_enable_i                                  ),
      .scan_data_i             (/* Unconnected */                              ),
      .scan_data_o             (/* Unconnected */                              ),
      .tile_id_i               (id                                             ),
      // TCDM Master interfaces
      .tcdm_master_req_o       (tran_tcdm_master_req                           ),
      .tcdm_master_req_valid_o (tran_tcdm_master_req_valid                     ),
      .tcdm_master_req_ready_i (tran_tcdm_master_req_ready                     ),
      .tcdm_master_resp_i      (tran_tcdm_master_resp                          ),
      .tcdm_master_resp_valid_i(tran_tcdm_master_resp_valid                    ),
      .tcdm_master_resp_ready_o(tran_tcdm_master_resp_ready                    ),
      // TCDM banks interface
      .tcdm_slave_req_i        (tran_tcdm_slave_req                            ),
      .tcdm_slave_req_valid_i  (tran_tcdm_slave_req_valid                      ),
      .tcdm_slave_req_ready_o  (tran_tcdm_slave_req_ready                      ),
      .tcdm_slave_resp_o       (tran_tcdm_slave_resp                           ),
      .tcdm_slave_resp_valid_o (tran_tcdm_slave_resp_valid                     ),
      .tcdm_slave_resp_ready_i (tran_tcdm_slave_resp_ready                     ),
      // TCDM DMA interfaces
      .tcdm_dma_req_i          (tcdm_dma_req_i[t]                              ),
      .tcdm_dma_req_valid_i    (tcdm_dma_req_valid_i[t]                        ),
      .tcdm_dma_req_ready_o    (tcdm_dma_req_ready_o[t]                        ),
      .tcdm_dma_resp_o         (tcdm_dma_resp_o[t]                             ),
      .tcdm_dma_resp_valid_o   (tcdm_dma_resp_valid_o[t]                       ),
      .tcdm_dma_resp_ready_i   (tcdm_dma_resp_ready_i[t]                       ),
      // AXI interface
      .axi_mst_req_o           (axi_tile_req[t]                                ),
      .axi_mst_resp_i          (axi_tile_resp[t]                               ),
      // Wake up interface
      .wake_up_i               (wake_up_i[t*NumCoresPerTile +: NumCoresPerTile])
    );

    // Transpose the group requests
    for (genvar g = 0; g < NumGroups; g++) begin: gen_tran_group_req
      assign tcdm_master_req[g][t]          = tran_tcdm_master_req[g];
      assign tcdm_master_req_valid[g][t]    = tran_tcdm_master_req_valid[g];
      assign tran_tcdm_master_req_ready[g]  = tcdm_master_req_ready[g][t];
      assign tran_tcdm_master_resp[g]       = tcdm_master_resp[g][t];
      assign tran_tcdm_master_resp_valid[g] = tcdm_master_resp_valid[g][t];
      assign tcdm_master_resp_ready[g][t]   = tran_tcdm_master_resp_ready[g];
      assign tran_tcdm_slave_req[g]         = tcdm_slave_req[g][t];
      assign tran_tcdm_slave_req_valid[g]   = tcdm_slave_req_valid[g][t];
      assign tcdm_slave_req_ready[g][t]     = tran_tcdm_slave_req_ready[g];
      assign tcdm_slave_resp[g][t]          = tran_tcdm_slave_resp[g];
      assign tcdm_slave_resp_valid[g][t]    = tran_tcdm_slave_resp_valid[g];
      assign tran_tcdm_slave_resp_ready[g]  = tcdm_slave_resp_ready[g][t];
    end: gen_tran_group_req
  end : gen_tiles

  /*********
   *  DMA  *
   *********/

  for (genvar d = 0; unsigned'(d) < NumDMAsPerGroup; d++) begin: gen_dmas
    localparam int unsigned a = NumTilesPerGroup + d;
    axi_dma_backend #(
      .DataWidth       (AxiDataWidth   ),
      .AddrWidth       (AddrWidth      ),
      .IdWidth         (AxiTileIdWidth ),
      .AxReqFifoDepth  (1              ),
      .TransFifoDepth  (1              ),
      .BufferDepth     (3              ),
      .axi_req_t       (axi_tile_req_t ),
      .axi_res_t       (axi_tile_resp_t),
      .burst_req_t     (dma_req_t      ),
      .DmaIdWidth      (1              ),
      .DmaTracing      (0              )
    ) i_axi_dma_backend (
      .clk_i            (clk_i             ),
      .rst_ni           (rst_ni            ),
      .dma_id_i         (1'b0              ),
      .axi_dma_req_o    (axi_tile_req[a]   ),
      .axi_dma_res_i    (axi_tile_resp[a]  ),
      .burst_req_i      (dma_req_i[d]      ),
      .valid_i          (dma_req_valid_i[d]),
      .ready_o          (dma_req_ready_o[d]),
      .backend_idle_o   (/*unused*/        ),
      .trans_complete_o (/*unused*/        )
    );

    // ------------------------------------------------------
    // AXI connection to EXT/TCDM
    // ------------------------------------------------------

    // xbar
    localparam int unsigned NumRules = 2;
    typedef struct packed {
      int unsigned idx;
      logic [AXI_ADDR_WIDTH-1:0] start_addr;
      logic [AXI_ADDR_WIDTH-1:0] end_addr;
    } xbar_rule_t;
    xbar_rule_t [NumRules-1:0] addr_map;
    logic [AXI_ADDR_WIDTH-1:0] cluster_base_addr;
    assign cluster_base_addr = 32'h1000_0000; /* + (cluster_id_i << 22);*/
    assign addr_map = '{
      '{ // SoC
        start_addr: '0,
        end_addr:   cluster_base_addr,
        idx:        0
      },
      '{ // TCDM
        start_addr: cluster_base_addr,
        end_addr:   cluster_base_addr + TCDM_SIZE,
        idx:        1
      }
    };

    localparam axi_pkg::xbar_cfg_t XbarCfg = '{
      NoSlvPorts:         1,
      NoMstPorts:         2,
      MaxMstTrans:        8,
      MaxSlvTrans:        8,
      FallThrough:        1'b0,
      LatencyMode:        axi_pkg::CUT_ALL_PORTS,
      AxiIdWidthSlvPorts: AxiTileIdWidth,
      AxiIdUsedSlvPorts:  AxiTileIdWidth,
      UniqueIds:          1'b0,
      AxiAddrWidth:       AddrWidth,
      AxiDataWidth:       AxiDataWidth,
      NoAddrRules:        NumRules
    };

    axi_xbar #(
      .Cfg          ( XbarCfg       ),
      .slv_aw_chan_t( slv_aw_chan_t ),
      .mst_aw_chan_t( mst_aw_chan_t ),
      .w_chan_t     ( w_chan_t      ),
      .slv_b_chan_t ( slv_b_chan_t  ),
      .mst_b_chan_t ( mst_b_chan_t  ),
      .slv_ar_chan_t( slv_ar_chan_t ),
      .mst_ar_chan_t( mst_ar_chan_t ),
      .slv_r_chan_t ( slv_r_chan_t  ),
      .mst_r_chan_t ( mst_r_chan_t  ),
      .slv_req_t    ( slv_req_t     ),
      .slv_resp_t   ( slv_resp_t    ),
      .mst_req_t    ( mst_req_t     ),
      .mst_resp_t   ( mst_resp_t    ),
      .rule_t       ( xbar_rule_t   )
    ) i_dma_axi_xbar (
      .clk_i                  ( clk_i                 ),
      .rst_ni                 ( rst_ni                ),
      .test_i                 ( test_mode_i           ),
      .slv_ports_req_i        ( dma_req          ),
      .slv_ports_resp_o       ( dma_rsp          ),
      .mst_ports_req_o        ( { tcdm_req, soc_req } ),
      .mst_ports_resp_i       ( { tcdm_rsp, soc_rsp } ),
      .addr_map_i             ( addr_map              ),
      .en_default_mst_port_i  ( '0                    ),
      .default_mst_port_i     ( '0                    )
    );

    // split AXI bus in read and write
    always_comb begin : proc_tcdm_axi_rw_split
      `AXI_SET_R_STRUCT(tcdm_rsp.r, tcdm_read_rsp.r)
      tcdm_rsp.r_valid        = tcdm_read_rsp.r_valid;
      tcdm_rsp.ar_ready       = tcdm_read_rsp.ar_ready;
      `AXI_SET_B_STRUCT(tcdm_rsp.b, tcdm_write_rsp.b)
      tcdm_rsp.b_valid        = tcdm_write_rsp.b_valid;
      tcdm_rsp.w_ready        = tcdm_write_rsp.w_ready;
      tcdm_rsp.aw_ready       = tcdm_write_rsp.aw_ready;

      tcdm_write_req          = '0;
      `AXI_SET_AW_STRUCT(tcdm_write_req.aw, tcdm_req.aw)
      tcdm_write_req.aw.addr  = tcdm_req.aw.addr[ADDR_WIDTH-1:0];
      tcdm_write_req.aw_valid = tcdm_req.aw_valid;
      `AXI_SET_W_STRUCT(tcdm_write_req.w, tcdm_req.w)
      tcdm_write_req.w_valid  = tcdm_req.w_valid;
      tcdm_write_req.b_ready  = tcdm_req.b_ready;

      tcdm_read_req           = '0;
      `AXI_SET_AR_STRUCT(tcdm_read_req.ar, tcdm_req.ar)
      tcdm_read_req.ar.addr   = tcdm_req.ar.addr[ADDR_WIDTH-1:0];
      tcdm_read_req.ar_valid  = tcdm_req.ar_valid;
      tcdm_read_req.r_ready   = tcdm_req.r_ready;
    end

    logic tcdm_master_we_0, tcdm_master_we_1, tcdm_master_we_2, tcdm_master_we_3;

    localparam TcdmFifoDepth = 1;

    axi_to_mem #(
      .axi_req_t   ( mem_req_t           ),
      .axi_resp_t  ( mst_resp_t          ),
      .AddrWidth   ( ADDR_WIDTH          ),
      .DataWidth   ( AXI_DATA_WIDTH      ),
      .IdWidth     ( MstIdxWidth         ),
      .NumBanks    ( 2                   ),
      .BufDepth    ( TcdmFifoDepth       )
    ) i_axi_to_mem_read (
      .clk_i        ( clk_i         ),
      .rst_ni       ( rst_ni        ),
      .busy_o       ( ),
      .axi_req_i    ( tcdm_read_req ),
      .axi_resp_o   ( tcdm_read_rsp ),
      .mem_req_o    ( { tcdm_master[0].req,     tcdm_master[1].req     } ),
      .mem_gnt_i    ( { tcdm_master[0].gnt,     tcdm_master[1].gnt     } ),
      .mem_addr_o   ( { tcdm_master[0].add,     tcdm_master[1].add     } ),
      .mem_wdata_o  ( { tcdm_master[0].data,    tcdm_master[1].data    } ),
      .mem_strb_o   ( { tcdm_master[0].be,      tcdm_master[1].be      } ),
      // .mem_atop_o   ( ),
      .mem_we_o     ( { tcdm_master_we_0,       tcdm_master_we_1       } ),
      .mem_rvalid_i ( { tcdm_master[0].r_valid, tcdm_master[1].r_valid } ),
      .mem_rdata_i  ( { tcdm_master[0].r_data,  tcdm_master[1].r_data  } )
    );

    axi_to_mem #(
      .axi_req_t   ( mem_req_t           ),
      .axi_resp_t  ( mst_resp_t          ),
      .AddrWidth   ( ADDR_WIDTH          ),
      .DataWidth   ( AXI_DATA_WIDTH      ),
      .IdWidth     ( MstIdxWidth         ),
      .NumBanks    ( 2                   ),
      .BufDepth    ( TcdmFifoDepth       )
    ) i_axi_to_mem_write (
      .clk_i        ( clk_i          ),
      .rst_ni       ( rst_ni         ),
      .busy_o       ( ),
      .axi_req_i    ( tcdm_write_req ),
      .axi_resp_o   ( tcdm_write_rsp ),
      .mem_req_o    ( { tcdm_master[2].req,     tcdm_master[3].req     } ),
      .mem_gnt_i    ( { tcdm_master[2].gnt,     tcdm_master[3].gnt     } ),
      .mem_addr_o   ( { tcdm_master[2].add,     tcdm_master[3].add     } ),
      .mem_wdata_o  ( { tcdm_master[2].data,    tcdm_master[3].data    } ),
      .mem_strb_o   ( { tcdm_master[2].be,      tcdm_master[3].be      } ),
      // .mem_atop_o   ( ),
      .mem_we_o     ( { tcdm_master_we_2,       tcdm_master_we_3       } ),
      .mem_rvalid_i ( { tcdm_master[2].r_valid, tcdm_master[3].r_valid } ),
      .mem_rdata_i  ( { tcdm_master[2].r_data,  tcdm_master[3].r_data  } )
    );

  end

  /*************************
   *  Local Interconnect  *
   *************************/

  // The local port is always at the index 0 out of the NumGroups TCDM ports of the tile.

  logic           [NumTilesPerGroup-1:0] master_local_req_valid;
  logic           [NumTilesPerGroup-1:0] master_local_req_ready;
  tcdm_addr_t     [NumTilesPerGroup-1:0] master_local_req_tgt_addr;
  logic           [NumTilesPerGroup-1:0] master_local_req_wen;
  tcdm_payload_t  [NumTilesPerGroup-1:0] master_local_req_wdata;
  strb_t          [NumTilesPerGroup-1:0] master_local_req_be;
  logic           [NumTilesPerGroup-1:0] master_local_resp_valid;
  logic           [NumTilesPerGroup-1:0] master_local_resp_ready;
  tcdm_payload_t  [NumTilesPerGroup-1:0] master_local_resp_rdata;
  logic           [NumTilesPerGroup-1:0] slave_local_req_valid;
  logic           [NumTilesPerGroup-1:0] slave_local_req_ready;
  tile_addr_t     [NumTilesPerGroup-1:0] slave_local_req_tgt_addr;
  tile_group_id_t [NumTilesPerGroup-1:0] slave_local_req_ini_addr;
  logic           [NumTilesPerGroup-1:0] slave_local_req_wen;
  tcdm_payload_t  [NumTilesPerGroup-1:0] slave_local_req_wdata;
  strb_t          [NumTilesPerGroup-1:0] slave_local_req_be;
  logic           [NumTilesPerGroup-1:0] slave_local_resp_valid;
  logic           [NumTilesPerGroup-1:0] slave_local_resp_ready;
  tile_group_id_t [NumTilesPerGroup-1:0] slave_local_resp_ini_addr;
  tcdm_payload_t  [NumTilesPerGroup-1:0] slave_local_resp_rdata;

  for (genvar t = 0; t < NumTilesPerGroup; t++) begin: gen_local_connections
    assign master_local_req_valid[t]     = tcdm_master_req_valid[0][t];
    assign master_local_req_tgt_addr[t]  = tcdm_master_req[0][t].tgt_addr;
    assign master_local_req_wen[t]       = tcdm_master_req[0][t].wen;
    assign master_local_req_wdata[t]     = tcdm_master_req[0][t].wdata;
    assign master_local_req_be[t]        = tcdm_master_req[0][t].be;
    assign tcdm_master_req_ready[0][t]   = master_local_req_ready[t];
    assign slave_local_resp_valid[t]     = tcdm_slave_resp_valid[0][t];
    assign slave_local_resp_ini_addr[t]  = tcdm_slave_resp[0][t].ini_addr;
    assign slave_local_resp_rdata[t]     = tcdm_slave_resp[0][t].rdata;
    assign tcdm_slave_resp_ready[0][t]   = slave_local_resp_ready[t];
    assign tcdm_master_resp_valid[0][t]  = master_local_resp_valid[t];
    assign tcdm_master_resp[0][t].rdata  = master_local_resp_rdata[t];
    assign master_local_resp_ready[t]    = tcdm_master_resp_ready[0][t];
    assign tcdm_slave_req_valid[0][t]    = slave_local_req_valid[t];
    assign tcdm_slave_req[0][t].tgt_addr = slave_local_req_tgt_addr[t];
    assign tcdm_slave_req[0][t].ini_addr = slave_local_req_ini_addr[t];
    assign tcdm_slave_req[0][t].wen      = slave_local_req_wen[t];
    assign tcdm_slave_req[0][t].wdata    = slave_local_req_wdata[t];
    assign tcdm_slave_req[0][t].be       = slave_local_req_be[t];
    assign slave_local_req_ready[t]      = tcdm_slave_req_ready[0][t];
  end

  variable_latency_interconnect #(
    .NumIn            (NumTilesPerGroup                             ),
    .NumOut           (NumTilesPerGroup                             ),
    .AddrWidth        (TCDMAddrWidth                                ),
    .DataWidth        ($bits(tcdm_payload_t)                        ),
    .BeWidth          (DataWidth/8                                  ),
    .ByteOffWidth     (0                                            ),
    .AddrMemWidth     (TCDMAddrMemWidth + idx_width(NumBanksPerTile)),
    .Topology         (tcdm_interconnect_pkg::LIC                   ),
    // The local interconnect needs no extra spill registers
    .SpillRegisterReq (64'b0                                        ),
    .SpillRegisterResp(64'b0                                        ),
    .AxiVldRdy        (1'b1                                         )
  ) i_local_interco (
    .clk_i          (clk_i                    ),
    .rst_ni         (rst_ni                   ),
    .req_valid_i    (master_local_req_valid   ),
    .req_ready_o    (master_local_req_ready   ),
    .req_tgt_addr_i (master_local_req_tgt_addr),
    .req_wen_i      (master_local_req_wen     ),
    .req_wdata_i    (master_local_req_wdata   ),
    .req_be_i       (master_local_req_be      ),
    .resp_valid_o   (master_local_resp_valid  ),
    .resp_ready_i   (master_local_resp_ready  ),
    .resp_rdata_o   (master_local_resp_rdata  ),
    .resp_ini_addr_i(slave_local_resp_ini_addr),
    .resp_rdata_i   (slave_local_resp_rdata   ),
    .resp_valid_i   (slave_local_resp_valid   ),
    .resp_ready_o   (slave_local_resp_ready   ),
    .req_valid_o    (slave_local_req_valid    ),
    .req_ready_i    (slave_local_req_ready    ),
    .req_be_o       (slave_local_req_be       ),
    .req_wdata_o    (slave_local_req_wdata    ),
    .req_wen_o      (slave_local_req_wen      ),
    .req_ini_addr_o (slave_local_req_ini_addr ),
    .req_tgt_addr_o (slave_local_req_tgt_addr )
  );

  /**************************
   *  Remote Interconnects  *
   **************************/

  for (genvar r = 1; r < NumGroups; r++) begin: gen_remote_interco
    logic           [NumTilesPerGroup-1:0] master_remote_req_valid;
    logic           [NumTilesPerGroup-1:0] master_remote_req_ready;
    tcdm_addr_t     [NumTilesPerGroup-1:0] master_remote_req_tgt_addr;
    logic           [NumTilesPerGroup-1:0] master_remote_req_wen;
    tcdm_payload_t  [NumTilesPerGroup-1:0] master_remote_req_wdata;
    strb_t          [NumTilesPerGroup-1:0] master_remote_req_be;
    logic           [NumTilesPerGroup-1:0] master_remote_resp_valid;
    logic           [NumTilesPerGroup-1:0] master_remote_resp_ready;
    tcdm_payload_t  [NumTilesPerGroup-1:0] master_remote_resp_rdata;
    logic           [NumTilesPerGroup-1:0] slave_remote_req_valid;
    logic           [NumTilesPerGroup-1:0] slave_remote_req_ready;
    tile_addr_t     [NumTilesPerGroup-1:0] slave_remote_req_tgt_addr;
    tile_group_id_t [NumTilesPerGroup-1:0] slave_remote_req_ini_addr;
    logic           [NumTilesPerGroup-1:0] slave_remote_req_wen;
    tcdm_payload_t  [NumTilesPerGroup-1:0] slave_remote_req_wdata;
    strb_t          [NumTilesPerGroup-1:0] slave_remote_req_be;
    logic           [NumTilesPerGroup-1:0] slave_remote_resp_valid;
    logic           [NumTilesPerGroup-1:0] slave_remote_resp_ready;
    tile_group_id_t [NumTilesPerGroup-1:0] slave_remote_resp_ini_addr;
    tcdm_payload_t  [NumTilesPerGroup-1:0] slave_remote_resp_rdata;

    for (genvar t = 0; t < NumTilesPerGroup; t++) begin: gen_remote_connections
      assign master_remote_req_valid[t]       = tcdm_master_req_valid[r][t];
      assign master_remote_req_tgt_addr[t]    = tcdm_master_req[r][t].tgt_addr;
      assign master_remote_req_wen[t]         = tcdm_master_req[r][t].wen;
      assign master_remote_req_wdata[t]       = tcdm_master_req[r][t].wdata;
      assign master_remote_req_be[t]          = tcdm_master_req[r][t].be;
      assign tcdm_master_req_ready[r][t]      = master_remote_req_ready[t];
      assign tcdm_master_req_valid_o[r][t]    = slave_remote_req_valid[t];
      assign tcdm_master_req_s[r][t].tgt_addr = slave_remote_req_tgt_addr[t];
      assign tcdm_master_req_s[r][t].ini_addr = slave_remote_req_ini_addr[t];
      assign tcdm_master_req_s[r][t].wen      = slave_remote_req_wen[t];
      assign tcdm_master_req_s[r][t].wdata    = slave_remote_req_wdata[t];
      assign tcdm_master_req_s[r][t].be       = slave_remote_req_be[t];
      assign slave_remote_req_ready[t]        = tcdm_master_req_ready_i[r][t];
      assign slave_remote_resp_valid[t]       = tcdm_slave_resp_valid[r][t];
      assign slave_remote_resp_ini_addr[t]    = tcdm_slave_resp[r][t].ini_addr;
      assign slave_remote_resp_rdata[t]       = tcdm_slave_resp[r][t].rdata;
      assign tcdm_slave_resp_ready[r][t]      = slave_remote_resp_ready[t];
      assign tcdm_slave_resp_valid_o[r][t]    = master_remote_resp_valid[t];
      assign tcdm_slave_resp_s[r][t].rdata    = master_remote_resp_rdata[t];
      assign master_remote_resp_ready[t]      = tcdm_slave_resp_ready_i[r][t];
    end: gen_remote_connections

    variable_latency_interconnect #(
      .NumIn              (NumTilesPerGroup                             ),
      .NumOut             (NumTilesPerGroup                             ),
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
   *  AXI Interconnect  *
   **********************/

  axi_tile_req_t   [NumAXIMastersPerGroup-1:0] axi_mst_req;
  axi_tile_resp_t  [NumAXIMastersPerGroup-1:0] axi_mst_resp;

  axi_hier_interco #(
    .NumSlvPorts    (NumTilesPerGroup+NumDMAsPerGroup),
    .NumMstPorts    (NumAXIMastersPerGroup           ),
    .Radix          (AxiHierRadix                    ),
    .EnableCache    (32'hFFFFFFFF                    ),
    .CacheLineWidth (ROCacheLineWidth                ),
    .CacheSizeByte  (ROCacheSizeByte                 ),
    .CacheSets      (ROCacheSets                     ),
    .AddrWidth      (AddrWidth                       ),
    .DataWidth      (AxiDataWidth                    ),
    .SlvIdWidth     (AxiTileIdWidth                  ),
    .MstIdWidth     (AxiTileIdWidth                  ),
    .UserWidth      (1                               ),
    .slv_req_t      (axi_tile_req_t                  ),
    .slv_resp_t     (axi_tile_resp_t                 ),
    .mst_req_t      (axi_tile_req_t                  ),
    .mst_resp_t     (axi_tile_resp_t                 )
  ) i_axi_interco (
    .clk_i           (clk_i          ),
    .rst_ni          (rst_ni         ),
    .test_i          (1'b0           ),
    .ro_cache_ctrl_i (ro_cache_ctrl_i),
    .slv_req_i       (axi_tile_req   ),
    .slv_resp_o      (axi_tile_resp  ),
    .mst_req_o       (axi_mst_req    ),
    .mst_resp_i      (axi_mst_resp   )
  );

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

endmodule: mempool_group
