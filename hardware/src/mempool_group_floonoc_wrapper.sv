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
#(
  // Parameters for mempool_group
  parameter addr_t       TCDMBaseAddr = 32'b0,
  parameter logic [31:0] BootAddr     = 32'h0000_1000,
) (
  // Clock and reset
  input  logic                                                         clk_i,
  input  logic                                                         rst_ni,
  input  logic                                                         testmode_i,
  // Scan chain
  input  logic                                                         scan_enable_i,
  input  logic                                                         scan_data_i,
  output logic                                                         scan_data_o,
  // Group ID
  input  logic           [idx_width(NumGroups)-1:0]                    group_id_i,

  // Router interface
  output floo_req_flit_t [NumTilesPerGroup-1:0]                        floo_req_o,
  output logic           [NumTilesPerGroup-1:0]                        floo_req_valid_o,
  input  logic           [NumTilesPerGroup-1:0]                        floo_req_ready_i,
  output floo_rsp_flit_t [NumTilesPerGroup-1:0]                        floo_rsp_o,
  output logic           [NumTilesPerGroup-1:0]                        floo_rsp_valid_o,
  input  logic           [NumTilesPerGroup-1:0]                        floo_rsp_ready_i,
  input  floo_req_flit_t [NumTilesPerGroup-1:0]                        floo_req_i,
  input  logic           [NumTilesPerGroup-1:0]                        floo_req_valid_i,
  output logic           [NumTilesPerGroup-1:0]                        floo_req_ready_o,
  input  floo_rsp_flit_t [NumTilesPerGroup-1:0]                        floo_rsp_i,
  input  logic           [NumTilesPerGroup-1:0]                        floo_rsp_valid_i,
  output logic           [NumTilesPerGroup-1:0]                        floo_rsp_ready_o

  // Wake up interface
  input  logic           [NumCoresPerGroup-1:0]                        wake_up_i,
  // RO-Cache configuration
  input  `STRUCT_PORT(ro_cache_ctrl_t)                                 ro_cache_ctrl_i,
  // DMA request
  input  `STRUCT_PORT(dma_req_t)                                       dma_req_i,
  input  logic                                                         dma_req_valid_i,
  output logic                                                         dma_req_ready_o,
  // DMA status
  output `STRUCT_PORT(dma_meta_t)                                      dma_meta_o,
   // AXI Interface
  output `STRUCT_VECT(axi_tile_req_t,     [NumAXIMastersPerGroup-1:0]) axi_mst_req_o,
  input  `STRUCT_VECT(axi_tile_resp_t,    [NumAXIMastersPerGroup-1:0]) axi_mst_resp_i
);

// TCDM Master interfaces
tcdm_master_req_t  [NumTilesPerGroup-1:0][NumRemotePortsPerTile-1:1]   tcdm_master_req;
logic              [NumTilesPerGroup-1:0][NumRemotePortsPerTile-1:1]   tcdm_master_req_valid;
logic              [NumTilesPerGroup-1:0][NumRemotePortsPerTile-1:1]   tcdm_master_req_ready;
tcdm_master_resp_t [NumTilesPerGroup-1:0][NumRemotePortsPerTile-1:1]   tcdm_master_resp;
logic              [NumTilesPerGroup-1:0][NumRemotePortsPerTile-1:1]   tcdm_master_resp_valid;
logic              [NumTilesPerGroup-1:0][NumRemotePortsPerTile-1:1]   tcdm_master_resp_ready;
// TCDM Slave interfaces
tcdm_slave_req_t   [NumTilesPerGroup-1:0][NumRemotePortsPerTile-1:1]   tcdm_slave_req;
logic              [NumTilesPerGroup-1:0][NumRemotePortsPerTile-1:1]   tcdm_slave_req_valid;
logic              [NumTilesPerGroup-1:0][NumRemotePortsPerTile-1:1]   tcdm_slave_req_ready;
tcdm_slave_resp_t  [NumTilesPerGroup-1:0][NumRemotePortsPerTile-1:1]   tcdm_slave_resp;
logic              [NumTilesPerGroup-1:0][NumRemotePortsPerTile-1:1]   tcdm_slave_resp_valid;
logic              [NumTilesPerGroup-1:0][NumRemotePortsPerTile-1:1]   tcdm_slave_resp_ready;

// Instantiate the mempool_group
mempool_group #(
  .TCDMBaseAddr            (TCDMBaseAddr),
  .BootAddr                (BootAddr)
) i_mempool_group (
  .clk_i                   (clk_i),
  .rst_ni                  (rst_ni),
  .testmode_i              (testmode_i),
  .scan_enable_i           (scan_enable_i),
  .scan_data_i             (scan_data_i),
  .scan_data_o             (scan_data_o),
  .group_id_i              (group_id_i),
  .tcdm_master_req_o       (tcdm_master_req),
  .tcdm_master_req_valid_o (tcdm_master_req_valid),
  .tcdm_master_req_ready_i (tcdm_master_req_ready),
  .tcdm_master_resp_i      (tcdm_master_resp),
  .tcdm_master_resp_valid_i(tcdm_master_resp_valid),
  .tcdm_master_resp_ready_o(tcdm_master_resp_ready),
  .tcdm_slave_req_i        (tcdm_slave_req),
  .tcdm_slave_req_valid_i  (tcdm_slave_req_valid),
  .tcdm_slave_req_ready_o  (tcdm_slave_req_ready),
  .tcdm_slave_resp_o       (tcdm_slave_resp),
  .tcdm_slave_resp_valid_o (tcdm_slave_resp_valid),
  .tcdm_slave_resp_ready_i (tcdm_slave_resp_ready),
  .wake_up_i               (wake_up_i),
  .ro_cache_ctrl_i         (ro_cache_ctrl_i),
  .dma_req_i               (dma_req_i),
  .dma_req_valid_i         (dma_req_valid_i),
  .dma_req_ready_o         (dma_req_ready_o),
  .dma_meta_o              (dma_meta_o),
  .axi_mst_req_o           (axi_mst_req_o),
  .axi_mst_resp_i          (axi_mst_resp_i)
);


// Instantiate the floo_tcdm_chimney for each tile
tcdm_req_t  [NumTilesPerGroup-1:0][NumRemotePortsPerTile-1:1] tcdm_req_to_chimney, tcdm_req_from_chimney;
tcdm_resp_t [NumTilesPerGroup-1:0][NumRemotePortsPerTile-1:1] tcdm_resp_to_chimney, tcdm_resp_from_chimney;

for (genvar i = 0; i < NumTilesPerGroup; i++) begin : gen_floo_tcdm_chimney_connection_i
  for (genvar j = 1; j < NumRemotePortsPerTile; j++) begin : gen_floo_tcdm_chimney_connection_j
    assign tcdm_req_to_chimney[i][j] = tcdm_req_t'{
      payload: tcdm_req_payload_t'{
        amo : tcdm_master_req.wdata.amo,
        wen : tcdm_master_req.wen,
        be  : tcdm_master_req.be,
        data: tcdm_master_req.wdata.data
      },
      meta: tcdm_req_meta_t'{
        meta_id : tcdm_master_req.wdata.meta_id,
        core_id : tcdm_master_req.wdata.core_id,
        tile_id : i,
        group_id: group_id_i,
        tgt_addr: tcdm_master_req.tgt_addr
      }
    };

    assign tcdm_resp_to_chimney[i][j] = tcdm_resp_t'{
      payload: tcdm_resp_payload_t'{
        amo : tcdm_slave_resp.rdata.amo,
        data: tcdm_slave_resp.rdata.data
      },
      meta: tcdm_resp_meta_t'{
        meta_id : tcdm_slave_resp.rdata.meta_id,
        core_id : tcdm_slave_resp.rdata.core_id,
        tile_id : tcdm_slave_resp.ini_addr,
        group_id: '0 // TODO: should get this info from group
      }
    };

    assign tcdm_master_resp[i][j] = tcdm_master_resp_t'{
      rdata: tcdm_payload_t'{
        meta_id : tcdm_resp_from_chimney.meta.meta_id,
        core_id : tcdm_resp_from_chimney.meta.core_id,
        amo     : tcdm_resp_from_chimney.payload.amo,
        data    : tcdm_resp_from_chimney.payload.data
      }
    };

    assign tcdm_slave_req[i][j] = tcdm_slave_req_t'{
      wdata: tcdm_payload_t'{
        meta_id : tcdm_req_from_chimney.meta.meta_id,
        core_id : tcdm_req_from_chimney.meta.core_id,
        amo     : tcdm_req_from_chimney.payload.amo,
        data    : tcdm_req_from_chimney.payload.data
      },
      wen     : tcdm_req_from_chimney.payload.wen,
      be      : tcdm_req_from_chimney.payload.be,
      tgt_addr: tcdm_req_from_chimney.meta.tgt_addr,
      ini_addr: tcdm_req_from_chimney.meta.group_id
    };

    floo_tcdm_chimney #(
      .tcdm_req_t        (tcdm_req_t),
      .tcdm_rsp_t        (tcdm_rsp_t),
      .floo_req_flit_t   (floo_req_flit_t),
      .floo_rsp_flit_t   (floo_rsp_flit_t),
      .id_t              (id_t),
      .RouteAlgo         (floo_pkg::XYRouting),
      .XYAddrOffsetX     (XYAddrOffsetX),
      .XYAddrOffsetY     (XYAddrOffsetY)
    ) u_floo_tcdm_chimney (
      .clk_i             (clk_i),
      .rst_ni            (rst_ni),
      /// TCDM to NoC interface
      .tcdm_req_i        (tcdm_req_to_chimney   [i][j]),
      .tcdm_req_valid_i  (tcdm_master_req_valid [i][j]),
      .tcdm_req_ready_o  (tcdm_master_req_ready [i][j]),
      .tcdm_rsp_o        (tcdm_resp_from_chimney[i][j]),
      .tcdm_rsp_valid_o  (tcdm_master_resp_valid[i][j]),
      .tcdm_rsp_ready_i  (tcdm_master_resp_ready[i][j]),
      /// NoC to TCDM interface
      .tcdm_req_o        (tcdm_req_from_chimney [i][j]),
      .tcdm_req_valid_o  (tcdm_slave_req_valid  [i][j]),
      .tcdm_req_ready_i  (tcdm_slave_req_ready  [i][j]),
      .tcdm_rsp_i        (tcdm_resp_to_chimney  [i][j]),
      .tcdm_rsp_valid_i  (tcdm_slave_resp_valid [i][j]),
      .tcdm_rsp_ready_o  (tcdm_slave_resp_ready [i][j]),
      // Coordinates/ID of the current tile
      .id_i              (group_id),
      // Routing table and address map
      .route_table_i     ('0),
      .addr_map_i        ('0),
      // Output to NoC
      .floo_req_o        (floo_req[i]),
      .floo_req_valid_o  (floo_req_valid[i]),
      .floo_req_ready_i  (floo_req_ready[i]),
      .floo_rsp_o        (floo_rsp[i]),
      .floo_rsp_valid_o  (floo_rsp_valid[i]),
      .floo_rsp_ready_i  (floo_rsp_ready[i]),
      // Input from NoC
      .floo_req_i        (floo_req[i]),
      .floo_req_valid_i  (floo_req_valid[i]),
      .floo_req_ready_o  (floo_req_ready[i]),
      .floo_rsp_i        (floo_rsp[i]),
      .floo_rsp_valid_i  (floo_rsp_valid[i]),
      .floo_rsp_ready_o  (floo_rsp_ready[i])
    );
  end : floo_tcdm_chimney_connection_j
end : floo_tcdm_chimney_connection_i



endmodule
