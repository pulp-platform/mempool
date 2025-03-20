// Copyright 2024 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "mempool/mempool.svh"
`include "reqrsp_interface/typedef.svh"
`include "common_cells/registers.svh"

module mempool_group_floonoc_wrapper
  import mempool_pkg::*;
  import cf_math_pkg::idx_width;
  import floo_pkg::*;
  import floo_terapool_noc_pkg::*;
#(
  // Parameters for mempool_group
  parameter addr_t       TCDMBaseAddr = 32'b0,
  parameter logic [31:0] BootAddr     = 32'h0000_1000
) (
  // Clock and reset
  input  logic                                                                          clk_i,
  input  logic                                                                          rst_ni,
  input  logic                                                                          testmode_i,
  // Scan chain
  input  logic                                                                          scan_enable_i,
  input  logic                                                                          scan_data_i,
  output logic                                                                          scan_data_o,
  // Group ID
  input  logic            [idx_width(NumGroups)-1:0]                                    group_id_i,
  input  id_t                                                                           floo_id_i,
  input  route_t          [NumEndpoints-1:0]                                            route_table_i,
  // Router interface
    // narrow req noc
  `ifdef USE_NARROW_REQ_CHANNEL
  output floo_tcdm_rd_req_t   [West:North][NumTilesPerGroup-1:0][NumNarrowRemoteReqPortsPerTile-1:0]                        floo_tcdm_narrow_req_o,
  output logic                [West:North][NumTilesPerGroup-1:0][NumNarrowRemoteReqPortsPerTile-1:0][NumVirtualChannel-1:0] floo_tcdm_narrow_req_valid_o,
  input  logic                [West:North][NumTilesPerGroup-1:0][NumNarrowRemoteReqPortsPerTile-1:0][NumVirtualChannel-1:0] floo_tcdm_narrow_req_ready_i,
  input  floo_tcdm_rd_req_t   [West:North][NumTilesPerGroup-1:0][NumNarrowRemoteReqPortsPerTile-1:0]                        floo_tcdm_narrow_req_i,
  input  logic                [West:North][NumTilesPerGroup-1:0][NumNarrowRemoteReqPortsPerTile-1:0][NumVirtualChannel-1:0] floo_tcdm_narrow_req_valid_i,
  output logic                [West:North][NumTilesPerGroup-1:0][NumNarrowRemoteReqPortsPerTile-1:0][NumVirtualChannel-1:0] floo_tcdm_narrow_req_ready_o,
  `endif

    // wide req noc
  output floo_tcdm_rdwr_req_t [West:North][NumTilesPerGroup-1:0][NumWideRemoteReqPortsPerTile-1:0]                          floo_tcdm_wide_req_o,
  output logic                [West:North][NumTilesPerGroup-1:0][NumWideRemoteReqPortsPerTile-1:0][NumVirtualChannel-1:0]   floo_tcdm_wide_req_valid_o,
  input  logic                [West:North][NumTilesPerGroup-1:0][NumWideRemoteReqPortsPerTile-1:0][NumVirtualChannel-1:0]   floo_tcdm_wide_req_ready_i,
  input  floo_tcdm_rdwr_req_t [West:North][NumTilesPerGroup-1:0][NumWideRemoteReqPortsPerTile-1:0]                          floo_tcdm_wide_req_i,
  input  logic                [West:North][NumTilesPerGroup-1:0][NumWideRemoteReqPortsPerTile-1:0][NumVirtualChannel-1:0]   floo_tcdm_wide_req_valid_i,
  output logic                [West:North][NumTilesPerGroup-1:0][NumWideRemoteReqPortsPerTile-1:0][NumVirtualChannel-1:0]   floo_tcdm_wide_req_ready_o,

    // wide resp noc
  output floo_tcdm_resp_t     [West:North][NumTilesPerGroup-1:0][NumRemoteRespPortsPerTile-1:1]                             floo_tcdm_resp_o,
  output logic                [West:North][NumTilesPerGroup-1:0][NumRemoteRespPortsPerTile-1:1][NumVirtualChannel-1:0]      floo_tcdm_resp_valid_o,
  input  logic                [West:North][NumTilesPerGroup-1:0][NumRemoteRespPortsPerTile-1:1][NumVirtualChannel-1:0]      floo_tcdm_resp_ready_i,
  input  floo_tcdm_resp_t     [West:North][NumTilesPerGroup-1:0][NumRemoteRespPortsPerTile-1:1]                             floo_tcdm_resp_i,
  input  logic                [West:North][NumTilesPerGroup-1:0][NumRemoteRespPortsPerTile-1:1][NumVirtualChannel-1:0]      floo_tcdm_resp_valid_i,
  output logic                [West:North][NumTilesPerGroup-1:0][NumRemoteRespPortsPerTile-1:1][NumVirtualChannel-1:0]      floo_tcdm_resp_ready_o,

  // AXI Router interface
  output floo_req_t           [West:North]                                                                                  floo_axi_req_o,
  output floo_rsp_t           [West:North]                                                                                  floo_axi_rsp_o,
  output floo_wide_t          [West:North]                                                                                  floo_axi_wide_o,
  input  floo_req_t           [West:North]                                                                                  floo_axi_req_i,
  input  floo_rsp_t           [West:North]                                                                                  floo_axi_rsp_i,
  input  floo_wide_t          [West:North]                                                                                  floo_axi_wide_i,

  // Wake up interface
  input  logic                [NumCoresPerGroup-1:0]                                                                        wake_up_i,
  // RO-Cache configuration
  input  `STRUCT_PORT(ro_cache_ctrl_t)                                                                                      ro_cache_ctrl_i,
  // DMA request
  input  `STRUCT_PORT(dma_req_t)                                                                                            dma_req_i,
  input  logic                                                                                                              dma_req_valid_i,
  output logic                                                                                                              dma_req_ready_o,
  // DMA status
  output `STRUCT_PORT(dma_meta_t)                                                                                           dma_meta_o
);

// Parse the address width to calculate the offset
localparam integer unsigned NumTilesPerGroupWidth = idx_width(NumTilesPerGroup);
localparam integer unsigned NumBanksPerTileWidth  = idx_width(NumBanksPerTile);
localparam integer unsigned TileBankRowOffset     = TCDMAddrMemWidth + NumBanksPerTileWidth;
localparam integer unsigned TileOffset            = NumBanksPerTileWidth + ByteOffset;

// TCDM Master interfaces
tcdm_master_req_t  [NumTilesPerGroup-1:0][NumRemoteReqPortsPerTile-1:1] tcdm_master_req;
logic              [NumTilesPerGroup-1:0][NumRemoteReqPortsPerTile-1:1] tcdm_master_req_valid;
logic              [NumTilesPerGroup-1:0][NumRemoteReqPortsPerTile-1:1] tcdm_master_req_ready;
tcdm_master_resp_t [NumTilesPerGroup-1:0][NumRemoteRespPortsPerTile-1:1] tcdm_master_resp;
logic              [NumTilesPerGroup-1:0][NumRemoteRespPortsPerTile-1:1] tcdm_master_resp_valid;
logic              [NumTilesPerGroup-1:0][NumRemoteRespPortsPerTile-1:1] tcdm_master_resp_ready;
// TCDM Slave interfaces
tcdm_slave_req_t   [NumTilesPerGroup-1:0][NumRemoteReqPortsPerTile-1:1] tcdm_slave_req;
logic              [NumTilesPerGroup-1:0][NumRemoteReqPortsPerTile-1:1] tcdm_slave_req_valid;
logic              [NumTilesPerGroup-1:0][NumRemoteReqPortsPerTile-1:1] tcdm_slave_req_ready;
tcdm_slave_resp_t  [NumTilesPerGroup-1:0][NumRemoteRespPortsPerTile-1:1] tcdm_slave_resp;
logic              [NumTilesPerGroup-1:0][NumRemoteRespPortsPerTile-1:1] tcdm_slave_resp_valid;
logic              [NumTilesPerGroup-1:0][NumRemoteRespPortsPerTile-1:1] tcdm_slave_resp_ready;

axi_tile_req_t  axi_mst_req;
axi_tile_resp_t axi_mst_resp;
axi_tile_req_t  axi_mst_req_from_group;
axi_tile_resp_t axi_mst_resp_to_group;
axi_tile_req_t  axi_mst_req_splitter;
axi_tile_resp_t axi_mst_resp_splitter;

// Instantiate the mempool_group
mempool_group #(
  .TCDMBaseAddr             (TCDMBaseAddr                   ),
  .BootAddr                 (BootAddr                       )
) i_mempool_group (
  .clk_i                    (clk_i                          ),
  .rst_ni                   (rst_ni                         ),
  .testmode_i               (testmode_i                     ),
  .scan_enable_i            (scan_enable_i                  ),
  .scan_data_i              (scan_data_i                    ),
  .scan_data_o              (scan_data_o                    ),
  .group_id_i               (group_id_i                     ),
  .tcdm_master_req_o        (tcdm_master_req                ),
  .tcdm_master_req_valid_o  (tcdm_master_req_valid          ),
  .tcdm_master_req_ready_i  (tcdm_master_req_ready          ),
  .tcdm_master_resp_i       (tcdm_master_resp               ),
  .tcdm_master_resp_valid_i (tcdm_master_resp_valid         ),
  .tcdm_master_resp_ready_o (tcdm_master_resp_ready         ),
  .tcdm_slave_req_i         (tcdm_slave_req                 ),
  .tcdm_slave_req_valid_i   (tcdm_slave_req_valid           ),
  .tcdm_slave_req_ready_o   (tcdm_slave_req_ready           ),
  .tcdm_slave_resp_o        (tcdm_slave_resp                ),
  .tcdm_slave_resp_valid_o  (tcdm_slave_resp_valid          ),
  .tcdm_slave_resp_ready_i  (tcdm_slave_resp_ready          ),
  .wake_up_i                (wake_up_i                      ),
  .ro_cache_ctrl_i          (ro_cache_ctrl_i                ),
  .dma_req_i                (dma_req_i                      ),
  .dma_req_valid_i          (dma_req_valid_i                ),
  .dma_req_ready_o          (dma_req_ready_o                ),
  .dma_meta_o               (dma_meta_o                     ),
  .axi_mst_req_o            (axi_mst_req_from_group         ),
  .axi_mst_resp_i           (axi_mst_resp_to_group          )
);

// Splitting logic based on DmaBurstLen and Interleave
generate
  if (DmaBurstLen > Interleave) begin : gen_axi_splitter
    axi_burst_splitter #(
      .MaxReadTxns  (16                             ),
      .MaxWriteTxns (16                             ),
      .AddrWidth    (AddrWidth                      ),
      .DataWidth    (AxiDataWidth                   ),
      .IdWidth      (AxiTileIdWidth                 ),
      .UserWidth    (1                              ),
      .axi_req_t    (axi_tile_req_t                 ),
      .axi_resp_t   (axi_tile_resp_t                )
    ) i_axi_burst_splitter (
      .clk_i        (clk_i                          ),
      .rst_ni       (rst_ni                         ),
      .slv_req_i    (axi_mst_req_from_group         ),
      .slv_resp_o   (axi_mst_resp_to_group          ),
      .mst_req_o    (axi_mst_req_splitter           ),
      .mst_resp_i   (axi_mst_resp_splitter          )
    );
  end else begin : gen_axi_splitter_bypass
    assign axi_mst_req_splitter = axi_mst_req_from_group;
    assign axi_mst_resp_to_group = axi_mst_resp_splitter;
  end
endgenerate

axi_L2_interleaver #(
  .NumAXIMasters            (1                              ),
  .NumL2                    (NumL2Banks                     ),
  .L2Size                   (L2Size                         )
) i_axi_L2_interleaver (
  .clk_i                    (clk_i                          ),
  .rst_ni                   (rst_ni                         ),
  .axi_l2_req_i             (axi_mst_req_splitter           ),
  .axi_l2_resp_o            (axi_mst_resp_splitter          ),
  .axi_l2_req_interleaved_o (axi_mst_req                    ),
  .axi_l2_resp_interleaved_i(axi_mst_resp                   )
);

// Instantiate the floo_tcdm_router for each tile
`ifdef USE_NARROW_REQ_CHANNEL
floo_tcdm_rd_req_t  [NumTilesPerGroup-1:0][NumNarrowRemoteReqPortsPerTile-1:0] floo_tcdm_rd_req_to_router,  floo_tcdm_rd_req_from_router;
floo_tcdm_rd_req_t  [NumTilesPerGroup-1:0][NumNarrowRemoteReqPortsPerTile-1:0] floo_tcdm_rd_req_from_router_vc;
logic               [NumTilesPerGroup-1:0][NumNarrowRemoteReqPortsPerTile-1:0] floo_tcdm_rd_req_to_router_valid;
logic               [NumTilesPerGroup-1:0][NumNarrowRemoteReqPortsPerTile-1:0] floo_tcdm_rd_req_to_router_ready;
logic               [NumTilesPerGroup-1:0][NumNarrowRemoteReqPortsPerTile-1:0][NumVirtualChannel-1:0] floo_tcdm_rd_req_to_router_vc_valid;
logic               [NumTilesPerGroup-1:0][NumNarrowRemoteReqPortsPerTile-1:0][NumVirtualChannel-1:0] floo_tcdm_rd_req_to_router_vc_ready;
logic               [NumTilesPerGroup-1:0][NumNarrowRemoteReqPortsPerTile-1:0][NumVirtualChannel-1:0] floo_tcdm_rd_req_from_router_vc_valid;
logic               [NumTilesPerGroup-1:0][NumNarrowRemoteReqPortsPerTile-1:0][NumVirtualChannel-1:0] floo_tcdm_rd_req_from_router_vc_ready;
`endif

floo_tcdm_rdwr_req_t[NumTilesPerGroup-1:0][NumWideRemoteReqPortsPerTile-1:0] floo_tcdm_rdwr_req_to_router,  floo_tcdm_rdwr_req_from_router;
floo_tcdm_rdwr_req_t[NumTilesPerGroup-1:0][NumWideRemoteReqPortsPerTile-1:0] floo_tcdm_rdwr_req_from_router_vc;
floo_tcdm_rdwr_req_t[NumTilesPerGroup-1:0][NumRemoteReqPortsPerTile-1:1] floo_tcdm_req_from_router;
floo_tcdm_resp_t    [NumTilesPerGroup-1:0][NumRemoteRespPortsPerTile-1:1] floo_tcdm_resp_to_router, floo_tcdm_resp_from_router;
logic               [NumTilesPerGroup-1:0][NumWideRemoteReqPortsPerTile-1:0] floo_tcdm_rdwr_req_to_router_valid;
logic               [NumTilesPerGroup-1:0][NumWideRemoteReqPortsPerTile-1:0] floo_tcdm_rdwr_req_to_router_ready;
logic               [NumTilesPerGroup-1:0][NumWideRemoteReqPortsPerTile-1:0][NumVirtualChannel-1:0] floo_tcdm_rdwr_req_to_router_vc_valid;
logic               [NumTilesPerGroup-1:0][NumWideRemoteReqPortsPerTile-1:0][NumVirtualChannel-1:0] floo_tcdm_rdwr_req_to_router_vc_ready;
logic               [NumTilesPerGroup-1:0][NumWideRemoteReqPortsPerTile-1:0][NumVirtualChannel-1:0] floo_tcdm_rdwr_req_from_router_vc_valid;
logic               [NumTilesPerGroup-1:0][NumWideRemoteReqPortsPerTile-1:0][NumVirtualChannel-1:0] floo_tcdm_rdwr_req_from_router_vc_ready;
logic               [NumTilesPerGroup-1:0][NumRemoteRespPortsPerTile-1:1] floo_tcdm_resp_to_router_valid;
logic               [NumTilesPerGroup-1:0][NumRemoteRespPortsPerTile-1:1] floo_tcdm_resp_to_router_ready;
logic               [NumTilesPerGroup-1:0][NumRemoteRespPortsPerTile-1:1][NumVirtualChannel-1:0] floo_tcdm_resp_to_router_vc_valid;
logic               [NumTilesPerGroup-1:0][NumRemoteRespPortsPerTile-1:1][NumVirtualChannel-1:0] floo_tcdm_resp_to_router_vc_ready;



// ------------------------------------------------------------------ //
// Remapping: From MemPool "Master Request" to FlooNoC "TCDM request" //
// ------------------------------------------------------------------ //
`ifdef REQ_REMAPPING

`ifdef USE_NARROW_REQ_CHANNEL
floo_tcdm_rd_req_t   [NumTilesPerGroup-1:0][NumNarrowRemoteReqPortsPerTile-1:0] floo_tcdm_rd_req_to_remapper;
logic       [NumTilesPerGroup-1:0][NumNarrowRemoteReqPortsPerTile-1:0] floo_tcdm_rd_req_to_remapper_valid;
logic       [NumTilesPerGroup-1:0][NumNarrowRemoteReqPortsPerTile-1:0] floo_tcdm_rd_req_to_remapper_ready;
`endif
floo_tcdm_rdwr_req_t [NumTilesPerGroup-1:0][NumWideRemoteReqPortsPerTile-1:0] floo_tcdm_rdwr_req_to_remapper;
logic       [NumTilesPerGroup-1:0][NumWideRemoteReqPortsPerTile-1:0] floo_tcdm_rdwr_req_to_remapper_valid;
logic       [NumTilesPerGroup-1:0][NumWideRemoteReqPortsPerTile-1:0] floo_tcdm_rdwr_req_to_remapper_ready;

for (genvar i = 0; i < NumTilesPerGroup; i++) begin : gen_master_req_to_remapper_req_i
  `ifdef USE_NARROW_REQ_CHANNEL
  for (genvar j = 0; j < NumNarrowRemoteReqPortsPerTile; j++) begin : gen_master_rd_req_to_remapper_req_j
    assign floo_tcdm_rd_req_to_remapper[i][j] = floo_tcdm_rd_req_t'{
      hdr: floo_tcdm_req_meta_t'{
        meta_id : tcdm_master_req[i][j+(1)].wdata.meta_id,              // For Register File
        core_id : tcdm_master_req[i][j+(1)].wdata.core_id,              // For Core
        src_tile_id : i,                                            // For Crossbar when response back
        src_id: group_xy_id_t'({group_id_i, 1'b0}),                         // For NoC Router when response back
        dst_id: group_xy_id_t'({tcdm_master_req[i][j].tgt_group_id, 1'b0}), // For NoC Router when request send
        tgt_addr: tcdm_master_req[i][j+(1)].tgt_addr,                   // For Crossbar when request send (bank rows per Group)
        last : 1'b1                                                 // Non Burst Request
      }
    };
    assign floo_tcdm_rd_req_to_remapper_valid[i][j] = tcdm_master_req_valid[i][j+(1)];
    assign tcdm_master_req_ready[i][j+(1)] = floo_tcdm_rd_req_to_remapper_ready[i][j];
  end : gen_master_rd_req_to_remapper_req_j
  `endif

  for (genvar j = 1 + NumNarrowRemoteReqPortsPerTile; j < NumRemoteReqPortsPerTile; j++) begin : gen_master_rdwr_wr_req_to_remapper_req_j
    assign floo_tcdm_rdwr_req_to_remapper[i][j-(1 + NumNarrowRemoteReqPortsPerTile)] = floo_tcdm_rdwr_req_t'{
      payload: floo_tcdm_req_payload_t'{
        amo : tcdm_master_req[i][j].wdata.amo,
        wen : tcdm_master_req[i][j].wen,
        be  : tcdm_master_req[i][j].be,
        data: tcdm_master_req[i][j].wdata.data
      },
      hdr: floo_tcdm_req_meta_t'{
        meta_id : tcdm_master_req[i][j].wdata.meta_id,                      // For Register File
        core_id : tcdm_master_req[i][j].wdata.core_id,                      // For Core
        src_tile_id : i,                                                    // For Crossbar when response back
        src_id: group_xy_id_t'({group_id_i, 1'b0}),                         // For NoC Router when response back
        dst_id: group_xy_id_t'({tcdm_master_req[i][j].tgt_group_id, 1'b0}), // For NoC Router when request send
        tgt_addr: tcdm_master_req[i][j].tgt_addr,                           // For Crossbar when request send (bank rows per Group)
        last : 1'b1                                                         // Non Burst Request
      }
    };
    assign floo_tcdm_rdwr_req_to_remapper_valid[i][j-(1 + NumNarrowRemoteReqPortsPerTile)] = tcdm_master_req_valid[i][j];
    assign tcdm_master_req_ready[i][j] = floo_tcdm_rdwr_req_to_remapper_ready[i][j-(1 + NumNarrowRemoteReqPortsPerTile)];
  end : gen_master_rdwr_wr_req_to_remapper_req_j
end : gen_master_req_to_remapper_req_i

`ifdef USE_NARROW_REQ_CHANNEL
floo_remapper #(
  .NumInp   (NumTilesPerGroup * NumNarrowRemoteReqPortsPerTile),
  .NumOut   (NumTilesPerGroup * NumNarrowRemoteReqPortsPerTile),
  .payload_t(floo_tcdm_rd_req_t)
) i_floo_tcdm_rd_req_remapper (
  .clk_i      (clk_i),
  .rst_ni     (rst_ni),
  .inp_data_i (floo_tcdm_rd_req_to_remapper),
  .inp_valid_i(floo_tcdm_rd_req_to_remapper_valid),
  .inp_ready_o(floo_tcdm_rd_req_to_remapper_ready),
  .oup_data_o (floo_tcdm_rd_req_to_router),
  .oup_valid_o(floo_tcdm_rd_req_to_router_valid),
  .oup_ready_i(floo_tcdm_rd_req_to_router_ready)
);
`endif

floo_remapper #(
  .NumInp   (NumTilesPerGroup * NumWideRemoteReqPortsPerTile),
  .NumOut   (NumTilesPerGroup * NumWideRemoteReqPortsPerTile),
  .payload_t(floo_tcdm_rdwr_req_t)
) i_floo_tcdm_rdwr_req_remapper (
  .clk_i      (clk_i),
  .rst_ni     (rst_ni),
  .inp_data_i (floo_tcdm_rdwr_req_to_remapper),
  .inp_valid_i(floo_tcdm_rdwr_req_to_remapper_valid),
  .inp_ready_o(floo_tcdm_rdwr_req_to_remapper_ready),
  .oup_data_o (floo_tcdm_rdwr_req_to_router),
  .oup_valid_o(floo_tcdm_rdwr_req_to_router_valid),
  .oup_ready_i(floo_tcdm_rdwr_req_to_router_ready)
);

`else

for (genvar i = 0; i < NumTilesPerGroup; i++) begin : gen_master_req_to_router_req_i
  `ifdef USE_NARROW_REQ_CHANNEL
  for (genvar j = 0; j < NumNarrowRemoteReqPortsPerTile; j++) begin : gen_master_rd_req_to_router_req_j
    assign floo_tcdm_rd_req_to_router[i][j] = floo_tcdm_rd_req_t'{
      hdr: floo_tcdm_req_meta_t'{
        meta_id : tcdm_master_req[i][j+(1)].wdata.meta_id,              // For Register File
        core_id : tcdm_master_req[i][j+(1)].wdata.core_id,              // For Core
        src_tile_id : i,                                                // For Crossbar when response back
        src_id: group_xy_id_t'({group_id_i, 1'b0}),                             // For NoC Router when response back
        dst_id: group_xy_id_t'({tcdm_master_req[i][j+(1)].tgt_group_id, 1'b0}), // For NoC Router when request send
        tgt_addr: tcdm_master_req[i][j+(1)].tgt_addr,                   // For Crossbar when request send (bank rows per Group)
        last : 1'b1                                                     // Non Burst Request
      }
    };
    assign floo_tcdm_rd_req_to_router_valid[i][j] = tcdm_master_req_valid[i][j+(1)];
    assign tcdm_master_req_ready[i][j+(1)] = floo_tcdm_rd_req_to_router_ready[i][j];
  end : gen_master_rd_req_to_router_req_j
  `endif

  for (genvar j = 1 + NumNarrowRemoteReqPortsPerTile; j < NumRemoteReqPortsPerTile; j++) begin : gen_master_rdwr_wr_req_to_router_req_j
    assign floo_tcdm_rdwr_req_to_router[i][j-(1 + NumNarrowRemoteReqPortsPerTile)] = floo_tcdm_rdwr_req_t'{
      payload: floo_tcdm_req_payload_t'{
        amo : tcdm_master_req[i][j].wdata.amo,
        wen : tcdm_master_req[i][j].wen,
        be  : tcdm_master_req[i][j].be,
        data: tcdm_master_req[i][j].wdata.data
      },
      hdr: floo_tcdm_req_meta_t'{
        meta_id : tcdm_master_req[i][j].wdata.meta_id,              // For Register File
        core_id : tcdm_master_req[i][j].wdata.core_id,              // For Core
        src_tile_id : i,                                            // For Crossbar when response back
        src_id: group_xy_id_t'({group_id_i, 1'b0}),                         // For NoC Router when response back
        dst_id: group_xy_id_t'({tcdm_master_req[i][j].tgt_group_id, 1'b0}), // For NoC Router when request send
        tgt_addr: tcdm_master_req[i][j].tgt_addr,                   // For Crossbar when request send (bank rows per Group)
        last : 1'b1                                                 // Non Burst Request
      }
    };
    assign floo_tcdm_rdwr_req_to_router_valid[i][j-(1 + NumNarrowRemoteReqPortsPerTile)] = tcdm_master_req_valid[i][j];
    assign tcdm_master_req_ready[i][j] = floo_tcdm_rdwr_req_to_router_ready[i][j-(1 + NumNarrowRemoteReqPortsPerTile)];
  end : gen_master_rdwr_wr_req_to_router_req_j
end : gen_master_req_to_router_req_i

`endif

`ifdef USE_NARROW_REQ_CHANNEL
for (genvar i = 0; i < NumTilesPerGroup; i++) begin : gen_master_rd_req_to_router_vc_req_i
  for (genvar j = 0; j < NumNarrowRemoteReqPortsPerTile; j++) begin : gen_master_rd_req_to_router_vc_req_j
    if(NumVirtualChannel == 1) begin
      assign floo_tcdm_rd_req_to_router_vc_valid[i][j][0] = floo_tcdm_rd_req_to_router_valid[i][j];
      assign floo_tcdm_rd_req_to_router_ready[i][j] = floo_tcdm_rd_req_to_router_vc_ready[i][j][0];
    end else begin
      floo_vc_mapper #(.NumVirtChannels(NumVirtualChannel)) i_floo_tcdm_rd_req_vc_mapper (
        .clk_i  (clk_i),
        .rst_ni (rst_ni),
        .valid_i(floo_tcdm_rd_req_to_router_valid[i][j]),
        .ready_o(floo_tcdm_rd_req_to_router_ready[i][j]),
        .valid_o(floo_tcdm_rd_req_to_router_vc_valid[i][j]),
        .ready_i(floo_tcdm_rd_req_to_router_vc_ready[i][j])
      );
    end
  end : gen_master_rd_req_to_router_vc_req_j
end : gen_master_rd_req_to_router_vc_req_i
`endif

for (genvar i = 0; i < NumTilesPerGroup; i++) begin : gen_master_rdwr_wr_req_to_router_vc_req_i
  for (genvar j = 0; j < NumWideRemoteReqPortsPerTile; j++) begin : gen_master_rdwr_wr_req_to_router_vc_req_j
    if(NumVirtualChannel == 1) begin
      assign floo_tcdm_rdwr_req_to_router_vc_valid[i][j][0] = floo_tcdm_rdwr_req_to_router_valid[i][j];
      assign floo_tcdm_rdwr_req_to_router_ready[i][j] = floo_tcdm_rdwr_req_to_router_vc_ready[i][j][0];
    end else begin
      floo_vc_mapper #(.NumVirtChannels(NumVirtualChannel)) i_floo_tcdm_rdwr_req_vc_mapper (
        .clk_i  (clk_i),
        .rst_ni (rst_ni),
        .valid_i(floo_tcdm_rdwr_req_to_router_valid[i][j]),
        .ready_o(floo_tcdm_rdwr_req_to_router_ready[i][j]),
        .valid_o(floo_tcdm_rdwr_req_to_router_vc_valid[i][j]),
        .ready_i(floo_tcdm_rdwr_req_to_router_vc_ready[i][j])
      );
    end
  end : gen_master_rdwr_wr_req_to_router_vc_req_j
end : gen_master_rdwr_wr_req_to_router_vc_req_i

// ------------------------------------------------------------------ //
// Crossbar: FlooNoC "TCDM request" input select target tile          //
// TODO: This is a consitent assignment to Tile's port,               //
//       Should be improved for confict resolution.                   //
// ------------------------------------------------------------------ //
tile_group_id_t       [NumTilesPerGroup-1:0][NumRemoteReqPortsPerTile-1:1] req_tile_sel;
floo_tcdm_rdwr_req_t  [NumTilesPerGroup-1:0][NumRemoteReqPortsPerTile-1:1] floo_tcdm_req_from_router_after_xbar;
logic                 [NumTilesPerGroup-1:0][NumRemoteReqPortsPerTile-1:1] floo_tcdm_req_from_router_after_xbar_valid;
logic                 [NumTilesPerGroup-1:0][NumRemoteReqPortsPerTile-1:1] floo_tcdm_req_from_router_after_xbar_ready;
logic                 [NumTilesPerGroup-1:0][NumRemoteReqPortsPerTile-1:1] floo_tcdm_req_from_router_before_xbar_valid;
logic                 [NumTilesPerGroup-1:0][NumRemoteReqPortsPerTile-1:1] floo_tcdm_req_from_router_before_xbar_ready;

generate
  for(genvar i = 0; i < NumTilesPerGroup; i++) begin: gen_floo_tcdm_req_from_router_i
    for (genvar j = 1; j < NumRemoteReqPortsPerTile; j++) begin : gen_floo_tcdm_req_from_router_j
      if(j < 1 + NumNarrowRemoteReqPortsPerTile) begin
        assign floo_tcdm_req_from_router[i][j].hdr      = floo_tcdm_rd_req_from_router[i][j-1].hdr;
        assign floo_tcdm_req_from_router[i][j].payload  = '0;
      end else begin
        assign floo_tcdm_req_from_router[i][j] = floo_tcdm_rdwr_req_from_router[i][j-(1+NumNarrowRemoteReqPortsPerTile)];
      end
    end : gen_floo_tcdm_req_from_router_j
  end : gen_floo_tcdm_req_from_router_i
endgenerate

if (NumTilesPerGroup == 1) begin
  assign req_tile_sel = '0;
end else begin
  for (genvar i = 0; i < NumTilesPerGroup; i++) begin : gen_req_sel_tgt_tile_i
    for (genvar j = 1; j < NumRemoteReqPortsPerTile; j++) begin : gen_req_sel_tgt_tile_j
      assign req_tile_sel[i][j] = floo_tcdm_req_from_router[i][j].hdr.tgt_addr[NumTilesPerGroupWidth-1:0];
    end : gen_req_sel_tgt_tile_j
  end : gen_req_sel_tgt_tile_i
end

tile_group_id_t     [NumRemoteReqPortsPerTile-1:1][NumTilesPerGroup-1:0] req_tile_sel_per_port;
floo_tcdm_rdwr_req_t[NumRemoteReqPortsPerTile-1:1][NumTilesPerGroup-1:0] floo_tcdm_req_from_router_per_port;
logic               [NumRemoteReqPortsPerTile-1:1][NumTilesPerGroup-1:0] floo_tcdm_req_from_router_before_xbar_valid_per_port;
logic               [NumRemoteReqPortsPerTile-1:1][NumTilesPerGroup-1:0] floo_tcdm_req_from_router_before_xbar_ready_per_port;

floo_tcdm_rdwr_req_t[NumRemoteReqPortsPerTile-1:1][NumTilesPerGroup-1:0] floo_tcdm_req_from_router_after_xbar_per_port;
logic               [NumRemoteReqPortsPerTile-1:1][NumTilesPerGroup-1:0] floo_tcdm_req_from_router_after_xbar_valid_per_port;
logic               [NumRemoteReqPortsPerTile-1:1][NumTilesPerGroup-1:0] floo_tcdm_req_from_router_after_xbar_ready_per_port;

for (genvar i = 0; i < NumTilesPerGroup; i++) begin : gen_floo_tcdm_req_from_router_per_port_i
  for (genvar j = 1; j < NumRemoteReqPortsPerTile; j++) begin : gen_floo_tcdm_req_from_router_per_port_j
    assign req_tile_sel_per_port                            [j][i] = req_tile_sel                           [i][j];
    assign floo_tcdm_req_from_router_per_port                    [j][i] = floo_tcdm_req_from_router                   [i][j];
    assign floo_tcdm_req_from_router_before_xbar_valid_per_port  [j][i] = floo_tcdm_req_from_router_before_xbar_valid [i][j];
    assign floo_tcdm_req_from_router_before_xbar_ready           [i][j] = floo_tcdm_req_from_router_before_xbar_ready_per_port  [j][i];

    assign floo_tcdm_req_from_router_after_xbar                  [i][j] = floo_tcdm_req_from_router_after_xbar_per_port       [j][i];
    assign floo_tcdm_req_from_router_after_xbar_valid            [i][j] = floo_tcdm_req_from_router_after_xbar_valid_per_port [j][i];
    assign floo_tcdm_req_from_router_after_xbar_ready_per_port   [j][i] = floo_tcdm_req_from_router_after_xbar_ready          [i][j];
  end : gen_floo_tcdm_req_from_router_per_port_j
end : gen_floo_tcdm_req_from_router_per_port_i

for (genvar i = 1; i < NumRemoteReqPortsPerTile; i++) begin : floo_tcdm_req_xbar
  stream_xbar #(
    .NumInp   (NumTilesPerGroup                                              ),
    .NumOut   (NumTilesPerGroup                                              ),
    .payload_t(floo_tcdm_rdwr_req_t                                          )
  ) i_local_req_interco (
    .clk_i  (clk_i                                                 ),
    .rst_ni (rst_ni                                                ),
    .flush_i(1'b0                                                  ),
    // External priority flag
    .rr_i   ('0                                                    ),
    // Master
    .data_i (floo_tcdm_req_from_router_per_port                    [i]        ),
    .valid_i(floo_tcdm_req_from_router_before_xbar_valid_per_port  [i]        ),
    .ready_o(floo_tcdm_req_from_router_before_xbar_ready_per_port  [i]        ),
    .sel_i  (req_tile_sel_per_port                                 [i]        ),
    // Slave
    .data_o (floo_tcdm_req_from_router_after_xbar_per_port         [i]        ),
    .valid_o(floo_tcdm_req_from_router_after_xbar_valid_per_port   [i]        ),
    .ready_i(floo_tcdm_req_from_router_after_xbar_ready_per_port   [i]        ),
    .idx_o  (/* Unused, TODO?: this is the data comes from index */           )
  );
end : floo_tcdm_req_xbar

// ------------------------------------------------------------------ //
// Remapping: From FlooNoC "TCDM request" to MemPool "Slave Request"  //
// ------------------------------------------------------------------ //
for (genvar i = 0; i < NumTilesPerGroup; i++) begin : gen_router_req_to_slave_req_i
  for (genvar j = 1; j < NumRemoteReqPortsPerTile; j++) begin : gen_router_req_to_slave_req_j
    assign tcdm_slave_req[i][j] = tcdm_slave_req_t'{
      wdata: tcdm_payload_t'{
        meta_id : floo_tcdm_req_from_router_after_xbar[i][j].hdr.meta_id,                        // For Register File
        core_id : floo_tcdm_req_from_router_after_xbar[i][j].hdr.core_id,                        // For Core
        amo     : floo_tcdm_req_from_router_after_xbar[i][j].payload.amo,
        data    : floo_tcdm_req_from_router_after_xbar[i][j].payload.data
      },
      wen     : floo_tcdm_req_from_router_after_xbar[i][j].payload.wen,
      be      : floo_tcdm_req_from_router_after_xbar[i][j].payload.be,
      // row | bank  <= row | bank | tile
      tgt_addr: floo_tcdm_req_from_router_after_xbar[i][j].hdr.tgt_addr[(NumTilesPerGroup == 1 ? 0 : NumTilesPerGroupWidth) +: (idx_width(NumBanksPerTile) + TCDMAddrMemWidth)], // For TCDM Bank, remove tile offset, it is selected by "req_tile_sel"
      ini_addr: floo_tcdm_req_from_router_after_xbar[i][j].hdr.src_tile_id,                      // For Crossbar when response back
      src_group_id: group_id_t'({floo_tcdm_req_from_router_after_xbar[i][j].hdr.src_id.x, floo_tcdm_req_from_router_after_xbar[i][j].hdr.src_id.y})           // For NoC Router when response back
    };
  assign tcdm_slave_req_valid[i][j] = floo_tcdm_req_from_router_after_xbar_valid[i][j];
  assign floo_tcdm_req_from_router_after_xbar_ready[i][j] = tcdm_slave_req_ready[i][j];
  end : gen_router_req_to_slave_req_j
end : gen_router_req_to_slave_req_i

// -------------------------------------------------------------------- //
// Remapping: From MemPool "Slave Response" to FlooNoC "TCDM Response" //
// -------------------------------------------------------------------- //
`ifdef RESP_REMAPPING

floo_tcdm_resp_t  [NumTilesPerGroup-1:0][NumRemoteRespPortsPerTile-1:1] floo_tcdm_resp_to_remapper;

for (genvar i = 0; i < NumTilesPerGroup; i++) begin : gen_slave_resp_to_remapper_resp_i
  for (genvar j = 1; j < NumRemoteRespPortsPerTile; j++) begin : gen_slave_resp_to_remapper_resp_j
    assign floo_tcdm_resp_to_remapper[i][j] = floo_tcdm_resp_t'{
      payload: floo_tcdm_resp_payload_t'{
        amo : tcdm_slave_resp[i][j].rdata.amo,
        data: tcdm_slave_resp[i][j].rdata.data
      },
      hdr: floo_tcdm_resp_meta_t'{
        meta_id : tcdm_slave_resp[i][j].rdata.meta_id,             // For Register File
        core_id : tcdm_slave_resp[i][j].rdata.core_id,             // For Core
        tile_id : tcdm_slave_resp[i][j].ini_addr,                  // For Crossbar when response back (Sender's Tile ID, propagated from request)
        src_id: group_xy_id_t'({group_id_i, 1'b0}),                // For NoC Router when response back
        dst_id: group_xy_id_t'({tcdm_slave_resp[i][j].src_group_id, 1'b0}),// For NoC Router when response back (Sender's Group ID, propagated from request)
        last : 1'b1                                                // Non Burst Request
      }
    };
  end : gen_slave_resp_to_remapper_resp_j
end : gen_slave_resp_to_remapper_resp_i

floo_remapper #(
  .NumInp   (NumTilesPerGroup * (NumRemoteRespPortsPerTile-1)),
  .NumOut   (NumTilesPerGroup * (NumRemoteRespPortsPerTile-1)),
  .payload_t(floo_tcdm_resp_t)
) i_floo_tcdm_resp_remapper (
  .clk_i      (clk_i),
  .rst_ni     (rst_ni),
  .inp_data_i (floo_tcdm_resp_to_remapper),
  .inp_valid_i(tcdm_slave_resp_valid),
  .inp_ready_o(tcdm_slave_resp_ready),
  .oup_data_o (floo_tcdm_resp_to_router),
  .oup_valid_o(floo_tcdm_resp_to_router_valid),
  .oup_ready_i(floo_tcdm_resp_to_router_ready)
);

`else

for (genvar i = 0; i < NumTilesPerGroup; i++) begin : gen_slave_resp_to_router_resp_i
  for (genvar j = 1; j < NumRemoteRespPortsPerTile; j++) begin : gen_slave_resp_to_router_resp_j
    assign floo_tcdm_resp_to_router[i][j] = floo_tcdm_resp_t'{
      payload: floo_tcdm_resp_payload_t'{
        amo : tcdm_slave_resp[i][j].rdata.amo,
        data: tcdm_slave_resp[i][j].rdata.data
      },
      hdr: floo_tcdm_resp_meta_t'{
        meta_id : tcdm_slave_resp[i][j].rdata.meta_id,             // For Register File
        core_id : tcdm_slave_resp[i][j].rdata.core_id,             // For Core
        tile_id : tcdm_slave_resp[i][j].ini_addr,                  // For Crossbar when response back (Sender's Tile ID, propagated from request)
        src_id: group_xy_id_t'({group_id_i, 1'b0}),                // For NoC Router when response back
        dst_id: group_xy_id_t'({tcdm_slave_resp[i][j].src_group_id, 1'b0}),// For NoC Router when response back (Sender's Group ID, propagated from request)
        last : 1'b1                                                // Non Burst Request
      }
    };
  end : gen_slave_resp_to_router_resp_j
end : gen_slave_resp_to_router_resp_i

assign floo_tcdm_resp_to_router_valid = tcdm_slave_resp_valid;
assign tcdm_slave_resp_ready = floo_tcdm_resp_to_router_ready;

`endif

for (genvar i = 0; i < NumTilesPerGroup; i++) begin : gen_slave_resp_to_router_vc_resp_i
  for (genvar j = 1; j < NumRemoteRespPortsPerTile; j++) begin : gen_slave_resp_to_router_vc_resp_j
    if(NumVirtualChannel == 1) begin
      assign floo_tcdm_resp_to_router_vc_valid[i][j][0] = floo_tcdm_resp_to_router_valid[i][j];
      assign floo_tcdm_resp_to_router_ready[i][j] = floo_tcdm_resp_to_router_vc_ready[i][j][0];
    end else begin
      floo_vc_mapper #(.NumVirtChannels(NumVirtualChannel)) i_floo_tcdm_resp_vc_mapper (
        .clk_i  (clk_i),
        .rst_ni (rst_ni),
        .valid_i(floo_tcdm_resp_to_router_valid[i][j]),
        .ready_o(floo_tcdm_resp_to_router_ready[i][j]),
        .valid_o(floo_tcdm_resp_to_router_vc_valid[i][j]),
        .ready_i(floo_tcdm_resp_to_router_vc_ready[i][j])
      );
    end
  end : gen_slave_resp_to_router_vc_resp_j
end : gen_slave_resp_to_router_vc_resp_i

// ------------------------------------------------------------------ //
// Crossbar: FlooNoC "TCDM reponse" input select target tile          //
// TODO: This is a consitent assignment to Tile's port,               //
//       Should be improved for confict resolution.                   //
// ------------------------------------------------------------------ //
tile_group_id_t [NumTilesPerGroup-1:0][NumRemoteRespPortsPerTile-1:1] resp_tile_sel;
floo_tcdm_resp_t[NumTilesPerGroup-1:0][NumRemoteRespPortsPerTile-1:1] floo_tcdm_resp_from_router_after_xbar;
logic           [NumTilesPerGroup-1:0][NumRemoteRespPortsPerTile-1:1] floo_tcdm_resp_from_router_after_xbar_valid;
logic           [NumTilesPerGroup-1:0][NumRemoteRespPortsPerTile-1:1] floo_tcdm_resp_from_router_after_xbar_ready;
logic           [NumTilesPerGroup-1:0][NumRemoteRespPortsPerTile-1:1] floo_tcdm_resp_from_router_before_xbar_valid;
logic           [NumTilesPerGroup-1:0][NumRemoteRespPortsPerTile-1:1] floo_tcdm_resp_from_router_before_xbar_ready;
floo_tcdm_resp_t[NumTilesPerGroup-1:0][NumRemoteRespPortsPerTile-1:1] floo_tcdm_resp_from_router_vc;
logic           [NumTilesPerGroup-1:0][NumRemoteRespPortsPerTile-1:1][NumVirtualChannel-1:0] floo_tcdm_resp_from_router_vc_valid;
logic           [NumTilesPerGroup-1:0][NumRemoteRespPortsPerTile-1:1][NumVirtualChannel-1:0] floo_tcdm_resp_from_router_vc_ready;

if (NumTilesPerGroup == 1) begin
  assign resp_tile_sel = '0;
end else begin
  for (genvar i = 0; i < NumTilesPerGroup; i++) begin : gen_resp_sel_tgt_tile_i
    for (genvar j = 1; j < NumRemoteRespPortsPerTile; j++) begin : gen_resp_sel_tgt_tile_j
      assign resp_tile_sel[i][j] = floo_tcdm_resp_from_router[i][j].hdr.tile_id;
    end : gen_resp_sel_tgt_tile_j
  end : gen_resp_sel_tgt_tile_i
end

tile_group_id_t [NumRemoteRespPortsPerTile-1:1][NumTilesPerGroup-1:0] resp_tile_sel_per_port;
floo_tcdm_resp_t[NumRemoteRespPortsPerTile-1:1][NumTilesPerGroup-1:0] floo_tcdm_resp_from_router_per_port;
logic           [NumRemoteRespPortsPerTile-1:1][NumTilesPerGroup-1:0] floo_tcdm_resp_from_router_before_xbar_valid_per_port;
logic           [NumRemoteRespPortsPerTile-1:1][NumTilesPerGroup-1:0] floo_tcdm_resp_from_router_before_xbar_ready_per_port;

floo_tcdm_resp_t[NumRemoteRespPortsPerTile-1:1][NumTilesPerGroup-1:0] floo_tcdm_resp_from_router_after_xbar_per_port;
logic           [NumRemoteRespPortsPerTile-1:1][NumTilesPerGroup-1:0] floo_tcdm_resp_from_router_after_xbar_valid_per_port;
logic           [NumRemoteRespPortsPerTile-1:1][NumTilesPerGroup-1:0] floo_tcdm_resp_from_router_after_xbar_ready_per_port;

for (genvar i = 0; i < NumTilesPerGroup; i++) begin : gen_floo_tcdm_resp_from_router_per_port_i
  for (genvar j = 1; j < NumRemoteRespPortsPerTile; j++) begin : gen_floo_tcdm_resp_from_router_per_port_j
    assign resp_tile_sel_per_port                                 [j][i] = resp_tile_sel                                          [i][j];
    assign floo_tcdm_resp_from_router_per_port                    [j][i] = floo_tcdm_resp_from_router                             [i][j];
    assign floo_tcdm_resp_from_router_before_xbar_valid_per_port  [j][i] = floo_tcdm_resp_from_router_before_xbar_valid           [i][j];
    assign floo_tcdm_resp_from_router_before_xbar_ready           [i][j] = floo_tcdm_resp_from_router_before_xbar_ready_per_port  [j][i];

    assign floo_tcdm_resp_from_router_after_xbar                  [i][j] = floo_tcdm_resp_from_router_after_xbar_per_port         [j][i];
    assign floo_tcdm_resp_from_router_after_xbar_valid            [i][j] = floo_tcdm_resp_from_router_after_xbar_valid_per_port   [j][i];
    assign floo_tcdm_resp_from_router_after_xbar_ready_per_port   [j][i] = floo_tcdm_resp_from_router_after_xbar_ready            [i][j];
  end : gen_floo_tcdm_resp_from_router_per_port_j
end : gen_floo_tcdm_resp_from_router_per_port_i


for (genvar i = 1; i < NumRemoteRespPortsPerTile; i++) begin : floo_tcdm_resp_xbar
  stream_xbar #(
    .NumInp   (NumTilesPerGroup                                    ),
    .NumOut   (NumTilesPerGroup                                    ),
    .payload_t(floo_tcdm_resp_t                                    )
  ) i_local_resp_interco (
    .clk_i  (clk_i                                                 ),
    .rst_ni (rst_ni                                                ),
    .flush_i(1'b0                                                  ),
    // External priority flag
    .rr_i   ('0                                                    ),
    // Master
    .data_i (floo_tcdm_resp_from_router_per_port                    [i] ),
    .valid_i(floo_tcdm_resp_from_router_before_xbar_valid_per_port  [i] ),
    .ready_o(floo_tcdm_resp_from_router_before_xbar_ready_per_port  [i] ),
    .sel_i  (resp_tile_sel_per_port                                 [i] ),
    // Slave
    .data_o (floo_tcdm_resp_from_router_after_xbar_per_port         [i] ),
    .valid_o(floo_tcdm_resp_from_router_after_xbar_valid_per_port   [i] ),
    .ready_i(floo_tcdm_resp_from_router_after_xbar_ready_per_port   [i] ),
    .idx_o  (/* Unused, TODO?: this is the data comes from index */     )
  );
end : floo_tcdm_resp_xbar

// --------------------------------------------------------------------- //
// Remapping: From FlooNoC "TCDM response" to MemPool "Master Response"  //
// --------------------------------------------------------------------- //
for (genvar i = 0; i < NumTilesPerGroup; i++) begin : gen_router_resp_to_master_resp_i
  for (genvar j = 1; j < NumRemoteRespPortsPerTile; j++) begin : gen_router_resp_to_master_resp_j
    assign tcdm_master_resp[i][j] = tcdm_master_resp_t'{
      rdata: tcdm_payload_t'{
        meta_id : floo_tcdm_resp_from_router_after_xbar[i][j].hdr.meta_id, // For Register File
        core_id : floo_tcdm_resp_from_router_after_xbar[i][j].hdr.core_id, // For Core
        amo     : floo_tcdm_resp_from_router_after_xbar[i][j].payload.amo,
        data    : floo_tcdm_resp_from_router_after_xbar[i][j].payload.data
      }
    };
    assign tcdm_master_resp_valid[i][j] = floo_tcdm_resp_from_router_after_xbar_valid[i][j];
    assign floo_tcdm_resp_from_router_after_xbar_ready[i][j] = tcdm_master_resp_ready[i][j];
  end : gen_router_resp_to_master_resp_j
end : gen_router_resp_to_master_resp_i

// ------------------------------------------------------------------ //
// ----------------------       Router      --------------------------//
// ------------------------------------------------------------------ //
// req narrow noc
`ifdef USE_NARROW_REQ_CHANNEL
floo_tcdm_rd_req_t    [NumTilesPerGroup-1:0][NumNarrowRemoteReqPortsPerTile-1:0][West:North] floo_tcdm_narrow_req_o_trans;
logic                 [NumTilesPerGroup-1:0][NumNarrowRemoteReqPortsPerTile-1:0][West:North][NumVirtualChannel-1:0] floo_tcdm_narrow_req_valid_o_trans;
logic                 [NumTilesPerGroup-1:0][NumNarrowRemoteReqPortsPerTile-1:0][West:North][NumVirtualChannel-1:0] floo_tcdm_narrow_req_ready_i_trans;
floo_tcdm_rd_req_t    [NumTilesPerGroup-1:0][NumNarrowRemoteReqPortsPerTile-1:0][West:North] floo_tcdm_narrow_req_i_trans;
logic                 [NumTilesPerGroup-1:0][NumNarrowRemoteReqPortsPerTile-1:0][West:North][NumVirtualChannel-1:0] floo_tcdm_narrow_req_valid_i_trans;
logic                 [NumTilesPerGroup-1:0][NumNarrowRemoteReqPortsPerTile-1:0][West:North][NumVirtualChannel-1:0] floo_tcdm_narrow_req_ready_o_trans;
`endif

// req wide noc
floo_tcdm_rdwr_req_t  [NumTilesPerGroup-1:0][NumWideRemoteReqPortsPerTile-1:0][West:North]   floo_tcdm_wide_req_o_trans;
logic                 [NumTilesPerGroup-1:0][NumWideRemoteReqPortsPerTile-1:0][West:North][NumVirtualChannel-1:0]   floo_tcdm_wide_req_valid_o_trans;
logic                 [NumTilesPerGroup-1:0][NumWideRemoteReqPortsPerTile-1:0][West:North][NumVirtualChannel-1:0]   floo_tcdm_wide_req_ready_i_trans;
floo_tcdm_rdwr_req_t  [NumTilesPerGroup-1:0][NumWideRemoteReqPortsPerTile-1:0][West:North]   floo_tcdm_wide_req_i_trans;
logic                 [NumTilesPerGroup-1:0][NumWideRemoteReqPortsPerTile-1:0][West:North][NumVirtualChannel-1:0]   floo_tcdm_wide_req_valid_i_trans;
logic                 [NumTilesPerGroup-1:0][NumWideRemoteReqPortsPerTile-1:0][West:North][NumVirtualChannel-1:0]   floo_tcdm_wide_req_ready_o_trans;


floo_tcdm_resp_t      [NumTilesPerGroup-1:0][NumRemoteRespPortsPerTile-1:1][West:North]      floo_tcdm_resp_o_trans;
logic                 [NumTilesPerGroup-1:0][NumRemoteRespPortsPerTile-1:1][West:North][NumVirtualChannel-1:0]      floo_tcdm_resp_valid_o_trans;
logic                 [NumTilesPerGroup-1:0][NumRemoteRespPortsPerTile-1:1][West:North][NumVirtualChannel-1:0]      floo_tcdm_resp_ready_i_trans;
floo_tcdm_resp_t      [NumTilesPerGroup-1:0][NumRemoteRespPortsPerTile-1:1][West:North]      floo_tcdm_resp_i_trans;
logic                 [NumTilesPerGroup-1:0][NumRemoteRespPortsPerTile-1:1][West:North][NumVirtualChannel-1:0]      floo_tcdm_resp_valid_i_trans;
logic                 [NumTilesPerGroup-1:0][NumRemoteRespPortsPerTile-1:1][West:North][NumVirtualChannel-1:0]      floo_tcdm_resp_ready_o_trans;

for (genvar i = 0; i < NumTilesPerGroup; i++) begin : gen_router_router_connection_i
  `ifdef USE_NARROW_REQ_CHANNEL
  for (genvar j = 0; j < NumNarrowRemoteReqPortsPerTile; j++) begin : gen_router_router_narrow_req_connection_j
    for (genvar k = North; k <= West; k++) begin: gen_router_router_narrow_req_connection_k
      assign floo_tcdm_narrow_req_o              [k][i][j] = floo_tcdm_narrow_req_o_trans       [i][j][k];
      assign floo_tcdm_narrow_req_valid_o        [k][i][j] = floo_tcdm_narrow_req_valid_o_trans [i][j][k];
      assign floo_tcdm_narrow_req_ready_o        [k][i][j] = floo_tcdm_narrow_req_ready_o_trans [i][j][k];

      assign floo_tcdm_narrow_req_i_trans        [i][j][k] = floo_tcdm_narrow_req_i             [k][i][j];
      assign floo_tcdm_narrow_req_ready_i_trans  [i][j][k] = floo_tcdm_narrow_req_ready_i       [k][i][j];
      assign floo_tcdm_narrow_req_valid_i_trans  [i][j][k] = floo_tcdm_narrow_req_valid_i       [k][i][j];
    end : gen_router_router_narrow_req_connection_k
  end : gen_router_router_narrow_req_connection_j
  `endif

  for (genvar j = 0; j < NumWideRemoteReqPortsPerTile; j++) begin : gen_router_router_wide_req_connection_j
    for (genvar k = North; k <= West; k++) begin: gen_router_router_wide_req_connection_k
      assign floo_tcdm_wide_req_o                [k][i][j] = floo_tcdm_wide_req_o_trans         [i][j][k];
      assign floo_tcdm_wide_req_valid_o          [k][i][j] = floo_tcdm_wide_req_valid_o_trans   [i][j][k];
      assign floo_tcdm_wide_req_ready_o          [k][i][j] = floo_tcdm_wide_req_ready_o_trans   [i][j][k];

      assign floo_tcdm_wide_req_i_trans          [i][j][k] = floo_tcdm_wide_req_i               [k][i][j];
      assign floo_tcdm_wide_req_ready_i_trans    [i][j][k] = floo_tcdm_wide_req_ready_i         [k][i][j];
      assign floo_tcdm_wide_req_valid_i_trans    [i][j][k] = floo_tcdm_wide_req_valid_i         [k][i][j];
    end : gen_router_router_wide_req_connection_k
  end : gen_router_router_wide_req_connection_j


  for (genvar j = 1; j < NumRemoteRespPortsPerTile; j++) begin : gen_router_router_wide_resp_connection_j
    for (genvar k = North; k <= West; k++) begin: gen_router_router_wide_resp_connection_k
      assign floo_tcdm_resp_o              [k][i][j] = floo_tcdm_resp_o_trans       [i][j][k];
      assign floo_tcdm_resp_valid_o        [k][i][j] = floo_tcdm_resp_valid_o_trans [i][j][k];
      assign floo_tcdm_resp_ready_o        [k][i][j] = floo_tcdm_resp_ready_o_trans [i][j][k];

      assign floo_tcdm_resp_i_trans        [i][j][k] = floo_tcdm_resp_i             [k][i][j];
      assign floo_tcdm_resp_ready_i_trans  [i][j][k] = floo_tcdm_resp_ready_i       [k][i][j];
      assign floo_tcdm_resp_valid_i_trans  [i][j][k] = floo_tcdm_resp_valid_i       [k][i][j];
    end : gen_router_router_wide_resp_connection_k
  end : gen_router_router_wide_resp_connection_j
end : gen_router_router_connection_i

`ifdef TORUS
  import routing_table_pkg::*;
  group_xy_id_t group_id;
  assign group_id = group_xy_id_t'(group_id_i);
`endif

for (genvar i = 0; i < NumTilesPerGroup; i++) begin : gen_router_router_i
  `ifdef USE_NARROW_REQ_CHANNEL
  for (genvar j = 0; j < NumNarrowRemoteReqPortsPerTile; j++) begin : gen_router_narrow_req_router_j
    floo_router #(
      .NumRoutes        (mempool_pkg::NumDirections),
      .NumVirtChannels  (mempool_pkg::NumVirtualChannel            ),
      .flit_t           (floo_tcdm_rd_req_t),
      .InFifoDepth      (mempool_pkg::NumRouterInFifoDepth), // Input buffer depth
      .OutFifoDepth     (mempool_pkg::NumRouterOutFifoDepth), // Output buffer depth, can try to set it to 0 for -1 cycle latency
    `ifdef TORUS
      .RouteAlgo        (IdTable      ),
      .id_t             (group_id_t   ),
      .NumAddrRules     (NumGroups    ),
      .addr_rule_t      (routing_rule_t)
    `else
      `ifdef O1_ROUTING
      .RouteAlgo        (O1Routing    ),
      `elsif ODD_EVEN_ROUTING
      .RouteAlgo        (OddEvenRouting    ),
      `else
      .RouteAlgo        (XYRouting    ),
      `endif
      .id_t             (group_xy_id_t),
      .NumAddrRules     (1            )
    `endif // TORUS
    ) i_floo_tcdm_narrow_req_router (
      .clk_i,
      .rst_ni,
      .test_enable_i  (1'b0                                                                   ),
      .xy_id_i        (group_xy_id_t'({group_id_i, 1'b0})                                    ),
      `ifdef TORUS
      .id_route_map_i (RoutingTables[group_id.x][group_id.y]                                  ),
      `else
      .id_route_map_i ('0                                                                     ),
      `endif
      .valid_i        ({floo_tcdm_rd_req_to_router_vc_valid[i][j],   floo_tcdm_narrow_req_valid_i_trans[i][j]}  ),
      .ready_o        ({floo_tcdm_rd_req_to_router_vc_ready[i][j],   floo_tcdm_narrow_req_ready_o_trans[i][j]}  ),
      .data_i         ({floo_tcdm_rd_req_to_router[i][j],            floo_tcdm_narrow_req_i_trans      [i][j]}  ),
      .valid_o        ({floo_tcdm_rd_req_from_router_vc_valid[i][j], floo_tcdm_narrow_req_valid_o_trans[i][j]}  ),
      .ready_i        ({floo_tcdm_rd_req_from_router_vc_ready[i][j], floo_tcdm_narrow_req_ready_i_trans[i][j]}  ),
      .data_o         ({floo_tcdm_rd_req_from_router_vc[i][j],       floo_tcdm_narrow_req_o_trans      [i][j]}  )
    );
    if(NumVirtualChannel == 1) begin
      assign floo_tcdm_rd_req_from_router[i][j] = floo_tcdm_rd_req_from_router_vc[i][j];
      assign floo_tcdm_req_from_router_before_xbar_valid[i][j+(1)] = floo_tcdm_rd_req_from_router_vc_valid[i][j];
      assign floo_tcdm_rd_req_from_router_vc_ready[i][j] = floo_tcdm_req_from_router_before_xbar_ready[i][j+(1)];
    end else begin
      floo_vc_mux #(.NumVirtChannels(NumVirtualChannel), .payload_t(floo_tcdm_rd_req_t)) i_floo_tcdm_rd_req_vc_mux (
        .clk_i  (clk_i),
        .rst_ni (rst_ni),
        .data_i (floo_tcdm_rd_req_from_router_vc[i][j]),
        .valid_i(floo_tcdm_rd_req_from_router_vc_valid[i][j]),
        .ready_o(floo_tcdm_rd_req_from_router_vc_ready[i][j]),
        .data_o (floo_tcdm_rd_req_from_router[i][j]),
        .valid_o(floo_tcdm_req_from_router_before_xbar_valid[i][j+(1)]),
        .ready_i(floo_tcdm_req_from_router_before_xbar_ready[i][j+(1)])
      );
    end
  end : gen_router_narrow_req_router_j
  `endif

  for (genvar j = 0; j < NumWideRemoteReqPortsPerTile; j++) begin : gen_router_wide_req_router_j
    floo_router #(
      .NumRoutes        (mempool_pkg::NumDirections),
      .NumVirtChannels  (NumVirtualChannel            ),
      .flit_t           (floo_tcdm_rdwr_req_t),
      .InFifoDepth      (mempool_pkg::NumRouterInFifoDepth), // Input buffer depth
      .OutFifoDepth     (mempool_pkg::NumRouterOutFifoDepth), // Output buffer depth, can try to set it to 0 for -1 cycle latency
    `ifdef TORUS
      .RouteAlgo        (IdTable      ),
      .id_t             (group_id_t   ),
      .NumAddrRules     (NumGroups    ),
      .addr_rule_t      (routing_rule_t)
    `else
      `ifdef O1_ROUTING
      .RouteAlgo        (O1Routing    ),
      `elsif ODD_EVEN_ROUTING
      .RouteAlgo        (OddEvenRouting    ),
      `else
      .RouteAlgo        (XYRouting    ),
      `endif
      .id_t             (group_xy_id_t),
      .NumAddrRules     (1            )
    `endif // TORUS
    ) i_floo_tcdm_wide_req_router (
      .clk_i,
      .rst_ni,
      .test_enable_i  (1'b0                                                            ),
      .xy_id_i        (group_xy_id_t'({group_id_i, 1'b0})                              ),
      `ifdef TORUS
      .id_route_map_i (RoutingTables[group_id.x][group_id.y]                                  ),
      `else
      .id_route_map_i ('0                                                                     ),
      `endif
      .valid_i        ({floo_tcdm_rdwr_req_to_router_vc_valid[i][j],   floo_tcdm_wide_req_valid_i_trans[i][j]}),
      .ready_o        ({floo_tcdm_rdwr_req_to_router_vc_ready[i][j],   floo_tcdm_wide_req_ready_o_trans[i][j]}),
      .data_i         ({floo_tcdm_rdwr_req_to_router[i][j],            floo_tcdm_wide_req_i_trans      [i][j]}),
      .valid_o        ({floo_tcdm_rdwr_req_from_router_vc_valid[i][j], floo_tcdm_wide_req_valid_o_trans[i][j]}),
      .ready_i        ({floo_tcdm_rdwr_req_from_router_vc_ready[i][j], floo_tcdm_wide_req_ready_i_trans[i][j]}),
      .data_o         ({floo_tcdm_rdwr_req_from_router_vc[i][j],       floo_tcdm_wide_req_o_trans      [i][j]})
    );
    if(NumVirtualChannel == 1) begin
      assign floo_tcdm_rdwr_req_from_router[i][j] = floo_tcdm_rdwr_req_from_router_vc[i][j];
      assign floo_tcdm_req_from_router_before_xbar_valid[i][j+(1+NumNarrowRemoteReqPortsPerTile)] = floo_tcdm_rdwr_req_from_router_vc_valid[i][j];
      assign floo_tcdm_rdwr_req_from_router_vc_ready[i][j] = floo_tcdm_req_from_router_before_xbar_ready[i][j+(1+NumNarrowRemoteReqPortsPerTile)];
    end else begin
      floo_vc_mux #(.NumVirtChannels(NumVirtualChannel), .payload_t(floo_tcdm_rdwr_req_t)) i_floo_tcdm_rdwr_req_vc_mux (
        .clk_i  (clk_i),
        .rst_ni (rst_ni),
        .data_i (floo_tcdm_rdwr_req_from_router_vc[i][j]),
        .valid_i(floo_tcdm_rdwr_req_from_router_vc_valid[i][j]),
        .ready_o(floo_tcdm_rdwr_req_from_router_vc_ready[i][j]),
        .data_o (floo_tcdm_rdwr_req_from_router[i][j]),
        .valid_o(floo_tcdm_req_from_router_before_xbar_valid[i][j+(1+NumNarrowRemoteReqPortsPerTile)]),
        .ready_i(floo_tcdm_req_from_router_before_xbar_ready[i][j+(1+NumNarrowRemoteReqPortsPerTile)])
      );
    end
  end : gen_router_wide_req_router_j

  for (genvar j = 1; j < NumRemoteRespPortsPerTile; j++) begin : gen_router_wide_resp_router_j
    floo_router #(
      .NumRoutes       (mempool_pkg::NumDirections),
      .NumVirtChannels (mempool_pkg::NumVirtualChannel            ),
      .flit_t          (floo_tcdm_resp_t  ),
      .InFifoDepth     (mempool_pkg::NumRouterInFifoDepth), // Input buffer depth
      .OutFifoDepth    (mempool_pkg::NumRouterOutFifoDepth), // Output buffer depth, can try to set it to 0 for -1 cycle latency
    `ifdef TORUS
      .RouteAlgo        (IdTable      ),
      .id_t             (group_id_t   ),
      .NumAddrRules     (NumGroups    ),
      .addr_rule_t      (routing_rule_t)
    `else
      `ifdef O1_ROUTING
      .RouteAlgo        (O1Routing    ),
      `elsif ODD_EVEN_ROUTING
      .RouteAlgo        (OddEvenRouting    ),
      `else
      .RouteAlgo        (XYRouting    ),
      `endif
      .id_t             (group_xy_id_t),
      .NumAddrRules     (1            )
    `endif // TORUS
    ) i_floo_tcdm_wide_resp_router (
      .clk_i,
      .rst_ni,
      .test_enable_i  (1'b0                                                              ),
      .xy_id_i        (group_xy_id_t'({group_id_i, 1'b0})                                ),
      `ifdef TORUS
      .id_route_map_i (RoutingTables[group_id.x][group_id.y]                                  ),
      `else
      .id_route_map_i ('0                                                                     ),
      `endif
      .valid_i        ({floo_tcdm_resp_to_router_vc_valid[i][j],   floo_tcdm_resp_valid_i_trans[i][j]}  ),
      .ready_o        ({floo_tcdm_resp_to_router_vc_ready[i][j],   floo_tcdm_resp_ready_o_trans[i][j]}  ),
      .data_i         ({floo_tcdm_resp_to_router[i][j],            floo_tcdm_resp_i_trans[i][j]}        ),
      .valid_o        ({floo_tcdm_resp_from_router_vc_valid[i][j], floo_tcdm_resp_valid_o_trans[i][j]}  ),
      .ready_i        ({floo_tcdm_resp_from_router_vc_ready[i][j], floo_tcdm_resp_ready_i_trans[i][j]}  ),
      .data_o         ({floo_tcdm_resp_from_router_vc[i][j],       floo_tcdm_resp_o_trans[i][j]}        )
    );
    if(NumVirtualChannel == 1) begin
      assign floo_tcdm_resp_from_router[i][j] = floo_tcdm_resp_from_router_vc[i][j];
      assign floo_tcdm_resp_from_router_before_xbar_valid[i][j] = floo_tcdm_resp_from_router_vc_valid[i][j];
      assign floo_tcdm_resp_from_router_vc_ready[i][j] = floo_tcdm_resp_from_router_before_xbar_ready[i][j];
    end else begin
      floo_vc_mux #(.NumVirtChannels(NumVirtualChannel), .payload_t(floo_tcdm_resp_t)) i_floo_tcdm_resp_vc_mux (
        .clk_i  (clk_i),
        .rst_ni (rst_ni),
        .data_i (floo_tcdm_resp_from_router_vc[i][j]),
        .valid_i(floo_tcdm_resp_from_router_vc_valid[i][j]),
        .ready_o(floo_tcdm_resp_from_router_vc_ready[i][j]),
        .data_o (floo_tcdm_resp_from_router[i][j]),
        .valid_o(floo_tcdm_resp_from_router_before_xbar_valid[i][j]),
        .ready_i(floo_tcdm_resp_from_router_before_xbar_ready[i][j])
      );
    end
  end : gen_router_wide_resp_router_j
end : gen_router_router_i

// ----------------------------- //
// AXI FlooNoC Network Interface //
// ----------------------------- //

floo_req_t  [Eject:North] floo_axi_req_out, floo_axi_req_in;
floo_rsp_t  [Eject:North] floo_axi_rsp_out, floo_axi_rsp_in;
floo_wide_t [Eject:North] floo_axi_wide_out, floo_axi_wide_in;

floo_nw_chimney #(
  .AxiCfgN             (AxiCfgN                                 ),
  .AxiCfgW             (AxiCfgW                                 ),
  .ChimneyCfgN         (set_ports(ChimneyDefaultCfg, 1'b0, 1'b0)),
  .ChimneyCfgW         (set_ports(ChimneyDefaultCfg, 1'b0, 1'b1)),
  .AtopSupport          ( '0                                    ),
  .RouteCfg            (RouteCfg                                ),
  .id_t                (id_t                                    ),
  .rob_idx_t           (rob_idx_t                               ),
  .route_t             (route_t                                 ),
  .dst_t               (route_t                                 ),
  .hdr_t               (hdr_t                                   ),
  .sam_rule_t          (sam_rule_t                              ),
  .Sam                 (Sam                                     ),
  .axi_narrow_in_req_t (axi_narrow_in_req_t                     ),
  .axi_narrow_in_rsp_t (axi_narrow_in_rsp_t                     ),
  .axi_narrow_out_req_t(axi_narrow_out_req_t                    ),
  .axi_narrow_out_rsp_t(axi_narrow_out_rsp_t                    ),
  .axi_wide_in_req_t   (axi_wide_in_req_t                       ),
  .axi_wide_in_rsp_t   (axi_wide_in_rsp_t                       ),
  .axi_wide_out_req_t  (axi_wide_out_req_t                      ),
  .axi_wide_out_rsp_t  (axi_wide_out_rsp_t                      ),
  .floo_req_t          (floo_req_t                              ),
  .floo_rsp_t          (floo_rsp_t                              ),
  .floo_wide_t         (floo_wide_t                             )
) i_floo_narrow_wide_chimney (
  .clk_i,
  .rst_ni,
  .test_enable_i        (testmode_i              ),
  .sram_cfg_i           ('0                      ),
  .axi_narrow_in_req_i  ('0                      ),
  .axi_narrow_in_rsp_o  (                        ),
  .axi_narrow_out_req_o (                        ),
  .axi_narrow_out_rsp_i ('0                      ),
  .axi_wide_in_req_i    (axi_mst_req             ),
  .axi_wide_in_rsp_o    (axi_mst_resp            ),
  .axi_wide_out_req_o   (                        ),
  .axi_wide_out_rsp_i   ('0                      ),
  .id_i                 (floo_id_i               ),
  .route_table_i,
  .floo_req_o           (floo_axi_req_in[Eject]  ),
  .floo_rsp_o           (floo_axi_rsp_in[Eject]  ),
  .floo_wide_o          (floo_axi_wide_in[Eject] ),
  .floo_req_i           (floo_axi_req_out[Eject] ),
  .floo_rsp_i           (floo_axi_rsp_out[Eject] ),
  .floo_wide_i          (floo_axi_wide_out[Eject])
);

// ----------------- //
// AXI FlooNoC Rouer //
// ----------------- //

floo_nw_router #(
  .AxiCfgN      ( AxiCfgN                     ),
  .AxiCfgW      ( AxiCfgW                     ),
  .RouteAlgo    ( RouteCfg.RouteAlgo          ),
  .NumRoutes    ( mempool_pkg::NumDirections  ),
  .InFifoDepth  ( 2                           ),
  .OutFifoDepth ( 2                           ),
  .id_t         ( id_t                        ),
  .hdr_t        ( hdr_t                       ),
  .floo_req_t   ( floo_req_t                  ),
  .floo_rsp_t   ( floo_rsp_t                  ),
  .floo_wide_t  ( floo_wide_t                 ),
  .NumAddrRules (1                            )
) i_floo_narrow_wide_router (
  .clk_i,
  .rst_ni,
  .test_enable_i  ( testmode_i        ),
  .id_i           ( '0                ),
  .id_route_map_i ( '0                ),
  .floo_req_i     ( floo_axi_req_in   ),
  .floo_rsp_i     ( floo_axi_rsp_in   ),
  .floo_req_o     ( floo_axi_req_out  ),
  .floo_rsp_o     ( floo_axi_rsp_out  ),
  .floo_wide_i    ( floo_axi_wide_in  ),
  .floo_wide_o    ( floo_axi_wide_out )
);

assign floo_axi_req_o  = floo_axi_req_out[West:North];
assign floo_axi_rsp_o  = floo_axi_rsp_out[West:North];
assign floo_axi_wide_o = floo_axi_wide_out[West:North];
assign floo_axi_req_in[West:North]  = floo_axi_req_i;
assign floo_axi_rsp_in[West:North]  = floo_axi_rsp_i;
assign floo_axi_wide_in[West:North] = floo_axi_wide_i;

endmodule
