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
  parameter logic [31:0] BootAddr     = 32'h0000_1000
) (
  // Clock and reset
  input  logic                                                                         clk_i,
  input  logic                                                                         rst_ni,
  input  logic                                                                         testmode_i,
  // Scan chain
  input  logic                                                                         scan_enable_i,
  input  logic                                                                         scan_data_i,
  output logic                                                                         scan_data_o,
  // Group ID
  input  logic           [idx_width(NumGroups)-1:0]                                    group_id_i,

  // Router interface
    // narrow req noc
  output floo_rd_req_t   [West:North][NumTilesPerGroup-1:0][NumNarrowRemoteReqPortsPerTile-1:0] floo_narrow_req_o,
  output logic           [West:North][NumTilesPerGroup-1:0][NumNarrowRemoteReqPortsPerTile-1:0] floo_narrow_req_valid_o,
  input  logic           [West:North][NumTilesPerGroup-1:0][NumNarrowRemoteReqPortsPerTile-1:0] floo_narrow_req_ready_i,
  input  floo_rd_req_t   [West:North][NumTilesPerGroup-1:0][NumNarrowRemoteReqPortsPerTile-1:0] floo_narrow_req_i,
  input  logic           [West:North][NumTilesPerGroup-1:0][NumNarrowRemoteReqPortsPerTile-1:0] floo_narrow_req_valid_i,
  output logic           [West:North][NumTilesPerGroup-1:0][NumNarrowRemoteReqPortsPerTile-1:0] floo_narrow_req_ready_o,

    // wide req noc
  output floo_rdwr_req_t [West:North][NumTilesPerGroup-1:0][NumWideRemoteReqPortsPerTile-1:0]   floo_wide_req_o,
  output logic           [West:North][NumTilesPerGroup-1:0][NumWideRemoteReqPortsPerTile-1:0]   floo_wide_req_valid_o,
  input  logic           [West:North][NumTilesPerGroup-1:0][NumWideRemoteReqPortsPerTile-1:0]   floo_wide_req_ready_i,
  input  floo_rdwr_req_t [West:North][NumTilesPerGroup-1:0][NumWideRemoteReqPortsPerTile-1:0]   floo_wide_req_i,
  input  logic           [West:North][NumTilesPerGroup-1:0][NumWideRemoteReqPortsPerTile-1:0]   floo_wide_req_valid_i,
  output logic           [West:North][NumTilesPerGroup-1:0][NumWideRemoteReqPortsPerTile-1:0]   floo_wide_req_ready_o,

    // wide resp noc
  output floo_resp_t     [West:North][NumTilesPerGroup-1:0][NumRemoteRespPortsPerTile-1:1]      floo_resp_o,
  output logic           [West:North][NumTilesPerGroup-1:0][NumRemoteRespPortsPerTile-1:1]      floo_resp_valid_o,
  input  logic           [West:North][NumTilesPerGroup-1:0][NumRemoteRespPortsPerTile-1:1]      floo_resp_ready_i,
  input  floo_resp_t     [West:North][NumTilesPerGroup-1:0][NumRemoteRespPortsPerTile-1:1]      floo_resp_i,
  input  logic           [West:North][NumTilesPerGroup-1:0][NumRemoteRespPortsPerTile-1:1]      floo_resp_valid_i,
  output logic           [West:North][NumTilesPerGroup-1:0][NumRemoteRespPortsPerTile-1:1]      floo_resp_ready_o,


  // Wake up interface
  input  logic           [NumCoresPerGroup-1:0]                                        wake_up_i,
  // RO-Cache configuration
  input  `STRUCT_PORT(ro_cache_ctrl_t)                                                 ro_cache_ctrl_i,
  // DMA request
  input  `STRUCT_PORT(dma_req_t)                                                       dma_req_i,
  input  logic                                                                         dma_req_valid_i,
  output logic                                                                         dma_req_ready_o,
  // DMA status
  output `STRUCT_PORT(dma_meta_t)                                                      dma_meta_o,
   // AXI Interface
  output `STRUCT_VECT(axi_tile_req_t,     [NumAXIMastersPerGroup-1:0])                 axi_mst_req_o,
  input  `STRUCT_VECT(axi_tile_resp_t,    [NumAXIMastersPerGroup-1:0])                 axi_mst_resp_i
);

// Parse the address width to calculate the offset
localparam integer unsigned NumTilesPerGroupWidth = idx_width(NumTilesPerGroup);
localparam integer unsigned NumBanksPerTileWidth = idx_width(NumBanksPerTile);
localparam integer unsigned TileBankRowOffset = TCDMAddrMemWidth + NumBanksPerTileWidth;
localparam integer unsigned TileOffset        = NumBanksPerTileWidth + ByteOffset;

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

// Instantiate the mempool_group
mempool_group #(
  .TCDMBaseAddr             (TCDMBaseAddr          ),
  .BootAddr                 (BootAddr              )
) i_mempool_group (
  .clk_i                    (clk_i                 ),
  .rst_ni                   (rst_ni                ),
  .testmode_i               (testmode_i            ),
  .scan_enable_i            (scan_enable_i         ),
  .scan_data_i              (scan_data_i           ),
  .scan_data_o              (scan_data_o           ),
  .group_id_i               (group_id_i            ),
  .tcdm_master_req_o        (tcdm_master_req       ),
  .tcdm_master_req_valid_o  (tcdm_master_req_valid ),
  .tcdm_master_req_ready_i  (tcdm_master_req_ready ),
  .tcdm_master_resp_i       (tcdm_master_resp      ),
  .tcdm_master_resp_valid_i (tcdm_master_resp_valid),
  .tcdm_master_resp_ready_o (tcdm_master_resp_ready),
  .tcdm_slave_req_i         (tcdm_slave_req        ),
  .tcdm_slave_req_valid_i   (tcdm_slave_req_valid  ),
  .tcdm_slave_req_ready_o   (tcdm_slave_req_ready  ),
  .tcdm_slave_resp_o        (tcdm_slave_resp       ),
  .tcdm_slave_resp_valid_o  (tcdm_slave_resp_valid ),
  .tcdm_slave_resp_ready_i  (tcdm_slave_resp_ready ),
  .wake_up_i                (wake_up_i             ),
  .ro_cache_ctrl_i          (ro_cache_ctrl_i       ),
  .dma_req_i                (dma_req_i             ),
  .dma_req_valid_i          (dma_req_valid_i       ),
  .dma_req_ready_o          (dma_req_ready_o       ),
  .dma_meta_o               (dma_meta_o            ),
  .axi_mst_req_o            (axi_mst_req_o         ),
  .axi_mst_resp_i           (axi_mst_resp_i        )
);

// Instantiate the floo_tcdm_router for each tile
floo_rd_req_t   [NumTilesPerGroup-1:0][NumNarrowRemoteReqPortsPerTile-1:0] floo_rd_req_to_router,  floo_rd_req_from_router;
floo_rdwr_req_t [NumTilesPerGroup-1:0][NumWideRemoteReqPortsPerTile-1:0] floo_rdwr_wr_req_to_router,  floo_rdwr_wr_req_from_router;
floo_rdwr_req_t [NumTilesPerGroup-1:0][NumRemoteReqPortsPerTile-1:1] floo_req_from_router;
floo_resp_t     [NumTilesPerGroup-1:0][NumRemoteRespPortsPerTile-1:1] floo_resp_to_router, floo_resp_from_router;

// ------------------------------------------------------------------ //
// Remapping: From MemPool "Master Request" to FlooNoC "TCDM request" //
// ------------------------------------------------------------------ //
for (genvar i = 0; i < NumTilesPerGroup; i++) begin : gen_master_req_to_router_req_i
  for (genvar j = 0; j < NumNarrowRemoteReqPortsPerTile; j++) begin : gen_master_rd_req_to_router_req_j
    assign floo_rd_req_to_router[i][j] = floo_rd_req_t'{
      hdr: floo_req_meta_t'{
        meta_id : tcdm_master_req[i][j+(1)].wdata.meta_id,              // For Register File
        core_id : tcdm_master_req[i][j+(1)].wdata.core_id,              // For Core
        src_tile_id : i,                                            // For Crossbar when response back
        src_id: group_xy_id_t'(group_id_i),                         // For NoC Router when response back
        dst_id: group_xy_id_t'(tcdm_master_req[i][j+(1)].tgt_group_id), // For NoC Router when request send
        tgt_addr: tcdm_master_req[i][j+(1)].tgt_addr,                   // For Crossbar when request send (bank rows per Group)
        last : 1'b1                                                 // Non Burst Request
      }
    };
  end : gen_master_rd_req_to_router_req_j

  for (genvar j = 1 + NumNarrowRemoteReqPortsPerTile; j < NumRemoteReqPortsPerTile; j++) begin : gen_master_rdwr_wr_req_to_router_req_j
    assign floo_rdwr_wr_req_to_router[i][j-(1 + NumNarrowRemoteReqPortsPerTile)] = floo_rdwr_req_t'{
      payload: floo_req_payload_t'{
        amo : tcdm_master_req[i][j].wdata.amo,
        wen : tcdm_master_req[i][j].wen,
        be  : tcdm_master_req[i][j].be,
        data: tcdm_master_req[i][j].wdata.data
      },
      hdr: floo_req_meta_t'{
        meta_id : tcdm_master_req[i][j].wdata.meta_id,              // For Register File
        core_id : tcdm_master_req[i][j].wdata.core_id,              // For Core
        src_tile_id : i,                                            // For Crossbar when response back
        src_id: group_xy_id_t'(group_id_i),                         // For NoC Router when response back
        dst_id: group_xy_id_t'(tcdm_master_req[i][j].tgt_group_id), // For NoC Router when request send
        tgt_addr: tcdm_master_req[i][j].tgt_addr,                   // For Crossbar when request send (bank rows per Group)
        last : 1'b1                                                 // Non Burst Request
      }
    };
  end : gen_master_rdwr_wr_req_to_router_req_j
end : gen_master_req_to_router_req_i

// ------------------------------------------------------------------ //
// Crossbar: FlooNoC "TCDM request" input select target tile          //
// TODO: This is a consitent assignment to Tile's port,               //
//       Should be improved for confict resolution.                   //
// ------------------------------------------------------------------ //
tile_group_id_t [NumTilesPerGroup-1:0][NumRemoteReqPortsPerTile-1:1] req_tile_sel;
floo_rdwr_req_t [NumTilesPerGroup-1:0][NumRemoteReqPortsPerTile-1:1] floo_req_from_router_after_xbar;
logic           [NumTilesPerGroup-1:0][NumRemoteReqPortsPerTile-1:1] floo_req_from_router_after_xbar_valid;
logic           [NumTilesPerGroup-1:0][NumRemoteReqPortsPerTile-1:1] floo_req_from_router_after_xbar_ready;
logic           [NumTilesPerGroup-1:0][NumRemoteReqPortsPerTile-1:1] floo_req_from_router_before_xbar_valid;
logic           [NumTilesPerGroup-1:0][NumRemoteReqPortsPerTile-1:1] floo_req_from_router_before_xbar_ready;

generate
  for(genvar i = 0; i < NumTilesPerGroup; i++) begin: gen_floo_req_from_router_i
    for (genvar j = 1; j < NumRemoteReqPortsPerTile; j++) begin : gen_floo_req_from_router_j
      if(j < 1 + NumNarrowRemoteReqPortsPerTile) begin
        assign floo_req_from_router[i][j].hdr      = floo_rd_req_from_router[i][j-1].hdr;
        assign floo_req_from_router[i][j].payload  = '0;
      end else begin
        assign floo_req_from_router[i][j] = floo_rdwr_wr_req_from_router[i][j-(1+NumNarrowRemoteReqPortsPerTile)];
      end
    end : gen_floo_req_from_router_j
  end : gen_floo_req_from_router_i
endgenerate

if (NumTilesPerGroup == 1) begin
  assign req_tile_sel = '0;
end else begin
  for (genvar i = 0; i < NumTilesPerGroup; i++) begin : gen_req_sel_tgt_tile_i
    for (genvar j = 1; j < NumRemoteReqPortsPerTile; j++) begin : gen_req_sel_tgt_tile_j
      assign req_tile_sel[i][j] = floo_req_from_router[i][j].hdr.tgt_addr[NumTilesPerGroupWidth-1:0];
    end : gen_req_sel_tgt_tile_j
  end : gen_req_sel_tgt_tile_i
end

tile_group_id_t [NumRemoteReqPortsPerTile-1:1][NumTilesPerGroup-1:0] req_tile_sel_per_port;
floo_rdwr_req_t [NumRemoteReqPortsPerTile-1:1][NumTilesPerGroup-1:0] floo_req_from_router_per_port;
logic           [NumRemoteReqPortsPerTile-1:1][NumTilesPerGroup-1:0] floo_req_from_router_before_xbar_valid_per_port;
logic           [NumRemoteReqPortsPerTile-1:1][NumTilesPerGroup-1:0] floo_req_from_router_before_xbar_ready_per_port;

floo_rdwr_req_t [NumRemoteReqPortsPerTile-1:1][NumTilesPerGroup-1:0] floo_req_from_router_after_xbar_per_port;
logic           [NumRemoteReqPortsPerTile-1:1][NumTilesPerGroup-1:0] floo_req_from_router_after_xbar_valid_per_port;
logic           [NumRemoteReqPortsPerTile-1:1][NumTilesPerGroup-1:0] floo_req_from_router_after_xbar_ready_per_port;

for (genvar i = 0; i < NumTilesPerGroup; i++) begin : gen_floo_req_from_router_per_port_i
  for (genvar j = 1; j < NumRemoteReqPortsPerTile; j++) begin : gen_floo_req_from_router_per_port_j
    assign req_tile_sel_per_port                            [j][i] = req_tile_sel                           [i][j];
    assign floo_req_from_router_per_port                    [j][i] = floo_req_from_router                   [i][j];
    assign floo_req_from_router_before_xbar_valid_per_port  [j][i] = floo_req_from_router_before_xbar_valid [i][j];
    assign floo_req_from_router_before_xbar_ready           [i][j] = floo_req_from_router_before_xbar_ready_per_port  [j][i];

    assign floo_req_from_router_after_xbar                  [i][j] = floo_req_from_router_after_xbar_per_port       [j][i];
    assign floo_req_from_router_after_xbar_valid            [i][j] = floo_req_from_router_after_xbar_valid_per_port [j][i];
    assign floo_req_from_router_after_xbar_ready_per_port   [j][i] = floo_req_from_router_after_xbar_ready          [i][j];
  end : gen_floo_req_from_router_per_port_j
end : gen_floo_req_from_router_per_port_i

for (genvar i = 1; i < NumRemoteReqPortsPerTile; i++) begin : floo_req_xbar
  stream_xbar #(
    .NumInp   (NumTilesPerGroup                                              ),
    .NumOut   (NumTilesPerGroup                                              ),
    .payload_t(floo_rdwr_req_t                                               )
  ) i_local_req_interco (
    .clk_i  (clk_i                                                           ),
    .rst_ni (rst_ni                                                          ),
    .flush_i(1'b0                                                            ),
    // External priority flag
    .rr_i   ('0                                                              ),
    // Master
    .data_i (floo_req_from_router_per_port                    [i]            ),
    .valid_i(floo_req_from_router_before_xbar_valid_per_port  [i]            ),
    .ready_o(floo_req_from_router_before_xbar_ready_per_port  [i]            ),
    .sel_i  (req_tile_sel_per_port                            [i]            ),
    // Slave
    .data_o (floo_req_from_router_after_xbar_per_port         [i]            ),
    .valid_o(floo_req_from_router_after_xbar_valid_per_port   [i]            ),
    .ready_i(floo_req_from_router_after_xbar_ready_per_port   [i]            ),
    .idx_o  (/* Unused, TODO?: this is the data comes from index */          )
  );
end : floo_req_xbar

// ------------------------------------------------------------------ //
// Remapping: From FlooNoC "TCDM request" to MemPool "Slave Request"  //
// ------------------------------------------------------------------ //
for (genvar i = 0; i < NumTilesPerGroup; i++) begin : gen_router_req_to_slave_req_i
  for (genvar j = 1; j < NumRemoteReqPortsPerTile; j++) begin : gen_router_req_to_slave_req_j
    assign tcdm_slave_req[i][j] = tcdm_slave_req_t'{
      wdata: tcdm_payload_t'{
        meta_id : floo_req_from_router_after_xbar[i][j].hdr.meta_id,                        // For Register File
        core_id : floo_req_from_router_after_xbar[i][j].hdr.core_id,                        // For Core
        amo     : floo_req_from_router_after_xbar[i][j].payload.amo,
        data    : floo_req_from_router_after_xbar[i][j].payload.data
      },
      wen     : floo_req_from_router_after_xbar[i][j].payload.wen,
      be      : floo_req_from_router_after_xbar[i][j].payload.be,
      // row | bank  <= row | bank | tile
      tgt_addr: floo_req_from_router_after_xbar[i][j].hdr.tgt_addr[(NumTilesPerGroup == 1 ? 0 : NumTilesPerGroupWidth) +: (idx_width(NumBanksPerTile) + TCDMAddrMemWidth)], // For TCDM Bank, remove tile offset, it is selected by "req_tile_sel"
      ini_addr: floo_req_from_router_after_xbar[i][j].hdr.src_tile_id,                      // For Crossbar when response back
      src_group_id: group_id_t'(floo_req_from_router_after_xbar[i][j].hdr.src_id)           // For NoC Router when response back
    };
  assign tcdm_slave_req_valid[i][j] = floo_req_from_router_after_xbar_valid[i][j];
  assign floo_req_from_router_after_xbar_ready[i][j] = tcdm_slave_req_ready[i][j];
  end : gen_router_req_to_slave_req_j
end : gen_router_req_to_slave_req_i

// -------------------------------------------------------------------- //
// Remapping: From MemPool "Slave Response" to FlooNoC "TCDM Response" //
// -------------------------------------------------------------------- //
for (genvar i = 0; i < NumTilesPerGroup; i++) begin : gen_slave_resp_to_router_resp_i
  for (genvar j = 1; j < NumRemoteReqPortsPerTile; j++) begin : gen_slave_resp_to_router_resp_j
    assign floo_resp_to_router[i][j] = floo_resp_t'{
      payload: floo_resp_payload_t'{
        amo : tcdm_slave_resp[i][j].rdata.amo,
        data: tcdm_slave_resp[i][j].rdata.data
      },
      hdr: floo_resp_meta_t'{
        meta_id : tcdm_slave_resp[i][j].rdata.meta_id,             // For Register File
        core_id : tcdm_slave_resp[i][j].rdata.core_id,             // For Core
        tile_id : tcdm_slave_resp[i][j].ini_addr,                  // For Crossbar when response back (Sender's Tile ID, propagated from request)
        dst_id: group_xy_id_t'(tcdm_slave_resp[i][j].src_group_id),// For NoC Router when response back (Sender's Group ID, propagated from request)
        last : 1'b1                                                // Non Burst Request
      }
    };
  end : gen_slave_resp_to_router_resp_j
end : gen_slave_resp_to_router_resp_i

// ------------------------------------------------------------------ //
// Crossbar: FlooNoC "TCDM reponse" input select target tile          //
// TODO: This is a consitent assignment to Tile's port,               //
//       Should be improved for confict resolution.                   //
// ------------------------------------------------------------------ //
tile_group_id_t [NumTilesPerGroup-1:0][NumRemoteRespPortsPerTile-1:1] resp_tile_sel;
floo_resp_t     [NumTilesPerGroup-1:0][NumRemoteRespPortsPerTile-1:1] floo_resp_from_router_after_xbar;
logic           [NumTilesPerGroup-1:0][NumRemoteRespPortsPerTile-1:1] floo_resp_from_router_after_xbar_valid;
logic           [NumTilesPerGroup-1:0][NumRemoteRespPortsPerTile-1:1] floo_resp_from_router_after_xbar_ready;
logic           [NumTilesPerGroup-1:0][NumRemoteRespPortsPerTile-1:1] floo_resp_from_router_before_xbar_valid;
logic           [NumTilesPerGroup-1:0][NumRemoteRespPortsPerTile-1:1] floo_resp_from_router_before_xbar_ready;

if (NumTilesPerGroup == 1) begin
  assign resp_tile_sel = '0;
end else begin
  for (genvar i = 0; i < NumTilesPerGroup; i++) begin : gen_resp_sel_tgt_tile_i
    for (genvar j = 1; j < NumRemoteReqPortsPerTile; j++) begin : gen_resp_sel_tgt_tile_j
      assign resp_tile_sel[i][j] = floo_resp_from_router[i][j].hdr.tile_id;
    end : gen_resp_sel_tgt_tile_j
  end : gen_resp_sel_tgt_tile_i
end

tile_group_id_t [NumRemoteRespPortsPerTile-1:1][NumTilesPerGroup-1:0] resp_tile_sel_per_port;
floo_resp_t     [NumRemoteRespPortsPerTile-1:1][NumTilesPerGroup-1:0] floo_resp_from_router_per_port;
logic           [NumRemoteRespPortsPerTile-1:1][NumTilesPerGroup-1:0] floo_resp_from_router_before_xbar_valid_per_port;
logic           [NumRemoteRespPortsPerTile-1:1][NumTilesPerGroup-1:0] floo_resp_from_router_before_xbar_ready_per_port;

floo_resp_t     [NumRemoteRespPortsPerTile-1:1][NumTilesPerGroup-1:0] floo_resp_from_router_after_xbar_per_port;
logic           [NumRemoteRespPortsPerTile-1:1][NumTilesPerGroup-1:0] floo_resp_from_router_after_xbar_valid_per_port;
logic           [NumRemoteRespPortsPerTile-1:1][NumTilesPerGroup-1:0] floo_resp_from_router_after_xbar_ready_per_port;

for (genvar i = 0; i < NumTilesPerGroup; i++) begin : gen_floo_resp_from_router_per_port_i
  for (genvar j = 1; j < NumRemoteRespPortsPerTile; j++) begin : gen_floo_resp_from_router_per_port_j
    assign resp_tile_sel_per_port                            [j][i] = resp_tile_sel                           [i][j];
    assign floo_resp_from_router_per_port                    [j][i] = floo_resp_from_router                   [i][j];
    assign floo_resp_from_router_before_xbar_valid_per_port  [j][i] = floo_resp_from_router_before_xbar_valid [i][j];
    assign floo_resp_from_router_before_xbar_ready           [i][j] = floo_resp_from_router_before_xbar_ready_per_port  [j][i];

    assign floo_resp_from_router_after_xbar                  [i][j] = floo_resp_from_router_after_xbar_per_port       [j][i];
    assign floo_resp_from_router_after_xbar_valid            [i][j] = floo_resp_from_router_after_xbar_valid_per_port [j][i];
    assign floo_resp_from_router_after_xbar_ready_per_port   [j][i] = floo_resp_from_router_after_xbar_ready          [i][j];
  end : gen_floo_resp_from_router_per_port_j
end : gen_floo_resp_from_router_per_port_i


for (genvar i = 1; i < NumRemoteRespPortsPerTile; i++) begin : floo_resp_xbar
  stream_xbar #(
    .NumInp   (NumTilesPerGroup                                               ),
    .NumOut   (NumTilesPerGroup                                               ),
    .payload_t(floo_resp_t                                                    )
  ) i_local_resp_interco (
    .clk_i  (clk_i                                                            ),
    .rst_ni (rst_ni                                                           ),
    .flush_i(1'b0                                                             ),
    // External priority flag
    .rr_i   ('0                                                               ),
    // Master
    .data_i (floo_resp_from_router_per_port                    [i]            ),
    .valid_i(floo_resp_from_router_before_xbar_valid_per_port  [i]            ),
    .ready_o(floo_resp_from_router_before_xbar_ready_per_port  [i]            ),
    .sel_i  (resp_tile_sel_per_port                            [i]            ),
    // Slave
    .data_o (floo_resp_from_router_after_xbar_per_port         [i]            ),
    .valid_o(floo_resp_from_router_after_xbar_valid_per_port   [i]            ),
    .ready_i(floo_resp_from_router_after_xbar_ready_per_port   [i]            ),
    .idx_o  (/* Unused, TODO?: this is the data comes from index */           )
  );
end : floo_resp_xbar

// --------------------------------------------------------------------- //
// Remapping: From FlooNoC "TCDM response" to MemPool "Master Response"  //
// --------------------------------------------------------------------- //
for (genvar i = 0; i < NumTilesPerGroup; i++) begin : gen_router_resp_to_master_resp_i
  for (genvar j = 1; j < NumRemoteRespPortsPerTile; j++) begin : gen_router_resp_to_master_resp_j
    assign tcdm_master_resp[i][j] = tcdm_master_resp_t'{
      rdata: tcdm_payload_t'{
        meta_id : floo_resp_from_router_after_xbar[i][j].hdr.meta_id, // For Register File
        core_id : floo_resp_from_router_after_xbar[i][j].hdr.core_id, // For Core
        amo     : floo_resp_from_router_after_xbar[i][j].payload.amo,
        data    : floo_resp_from_router_after_xbar[i][j].payload.data
      }
    };
    assign tcdm_master_resp_valid[i][j] = floo_resp_from_router_after_xbar_valid[i][j];
    assign floo_resp_from_router_after_xbar_ready[i][j] = tcdm_master_resp_ready[i][j];
  end : gen_router_resp_to_master_resp_j
end : gen_router_resp_to_master_resp_i

// ------------------------------------------------------------------ //
// ----------------------       Router      --------------------------//
// ------------------------------------------------------------------ //
// req narrow noc
floo_rd_req_t   [NumTilesPerGroup-1:0][NumNarrowRemoteReqPortsPerTile-1:0][West:North] floo_narrow_req_o_trans;
logic           [NumTilesPerGroup-1:0][NumNarrowRemoteReqPortsPerTile-1:0][West:North] floo_narrow_req_valid_o_trans;
logic           [NumTilesPerGroup-1:0][NumNarrowRemoteReqPortsPerTile-1:0][West:North] floo_narrow_req_ready_i_trans;
floo_rd_req_t   [NumTilesPerGroup-1:0][NumNarrowRemoteReqPortsPerTile-1:0][West:North] floo_narrow_req_i_trans;
logic           [NumTilesPerGroup-1:0][NumNarrowRemoteReqPortsPerTile-1:0][West:North] floo_narrow_req_valid_i_trans;
logic           [NumTilesPerGroup-1:0][NumNarrowRemoteReqPortsPerTile-1:0][West:North] floo_narrow_req_ready_o_trans;

// req wide noc
floo_rdwr_req_t [NumTilesPerGroup-1:0][NumWideRemoteReqPortsPerTile-1:0][West:North]   floo_wide_req_o_trans;
logic           [NumTilesPerGroup-1:0][NumWideRemoteReqPortsPerTile-1:0][West:North]   floo_wide_req_valid_o_trans;
logic           [NumTilesPerGroup-1:0][NumWideRemoteReqPortsPerTile-1:0][West:North]   floo_wide_req_ready_i_trans;
floo_rdwr_req_t [NumTilesPerGroup-1:0][NumWideRemoteReqPortsPerTile-1:0][West:North]   floo_wide_req_i_trans;
logic           [NumTilesPerGroup-1:0][NumWideRemoteReqPortsPerTile-1:0][West:North]   floo_wide_req_valid_i_trans;
logic           [NumTilesPerGroup-1:0][NumWideRemoteReqPortsPerTile-1:0][West:North]   floo_wide_req_ready_o_trans;


floo_resp_t     [NumTilesPerGroup-1:0][NumRemoteRespPortsPerTile-1:1][West:North]      floo_resp_o_trans;
logic           [NumTilesPerGroup-1:0][NumRemoteRespPortsPerTile-1:1][West:North]      floo_resp_valid_o_trans;
logic           [NumTilesPerGroup-1:0][NumRemoteRespPortsPerTile-1:1][West:North]      floo_resp_ready_i_trans;
floo_resp_t     [NumTilesPerGroup-1:0][NumRemoteRespPortsPerTile-1:1][West:North]      floo_resp_i_trans;
logic           [NumTilesPerGroup-1:0][NumRemoteRespPortsPerTile-1:1][West:North]      floo_resp_valid_i_trans;
logic           [NumTilesPerGroup-1:0][NumRemoteRespPortsPerTile-1:1][West:North]      floo_resp_ready_o_trans;

for (genvar i = 0; i < NumTilesPerGroup; i++) begin : gen_router_router_connection_i
  for (genvar j = 0; j < NumNarrowRemoteReqPortsPerTile; j++) begin : gen_router_router_narrow_req_connection_j
    for (genvar k = North; k <= West; k++) begin: gen_router_router_narrow_req_connection_k
      assign floo_narrow_req_o              [k][i][j] = floo_narrow_req_o_trans       [i][j][k];
      assign floo_narrow_req_valid_o        [k][i][j] = floo_narrow_req_valid_o_trans [i][j][k];
      assign floo_narrow_req_ready_o        [k][i][j] = floo_narrow_req_ready_o_trans [i][j][k];

      assign floo_narrow_req_i_trans        [i][j][k] = floo_narrow_req_i             [k][i][j];
      assign floo_narrow_req_ready_i_trans  [i][j][k] = floo_narrow_req_ready_i       [k][i][j];
      assign floo_narrow_req_valid_i_trans  [i][j][k] = floo_narrow_req_valid_i       [k][i][j];
    end : gen_router_router_narrow_req_connection_k
  end : gen_router_router_narrow_req_connection_j

  for (genvar j = 0; j < NumWideRemoteReqPortsPerTile; j++) begin : gen_router_router_wide_req_connection_j
    for (genvar k = North; k <= West; k++) begin: gen_router_router_wide_req_connection_k
      assign floo_wide_req_o                [k][i][j] = floo_wide_req_o_trans         [i][j][k];
      assign floo_wide_req_valid_o          [k][i][j] = floo_wide_req_valid_o_trans   [i][j][k];
      assign floo_wide_req_ready_o          [k][i][j] = floo_wide_req_ready_o_trans   [i][j][k];

      assign floo_wide_req_i_trans          [i][j][k] = floo_wide_req_i               [k][i][j];
      assign floo_wide_req_ready_i_trans    [i][j][k] = floo_wide_req_ready_i         [k][i][j];
      assign floo_wide_req_valid_i_trans    [i][j][k] = floo_wide_req_valid_i         [k][i][j];
    end : gen_router_router_wide_req_connection_k
  end : gen_router_router_wide_req_connection_j


  for (genvar j = 1; j < NumRemoteRespPortsPerTile; j++) begin : gen_router_router_wide_resp_connection_j
    for (genvar k = North; k <= West; k++) begin: gen_router_router_wide_resp_connection_k
      assign floo_resp_o              [k][i][j] = floo_resp_o_trans       [i][j][k];
      assign floo_resp_valid_o        [k][i][j] = floo_resp_valid_o_trans [i][j][k];
      assign floo_resp_ready_o        [k][i][j] = floo_resp_ready_o_trans [i][j][k];

      assign floo_resp_i_trans        [i][j][k] = floo_resp_i             [k][i][j];
      assign floo_resp_ready_i_trans  [i][j][k] = floo_resp_ready_i       [k][i][j];
      assign floo_resp_valid_i_trans  [i][j][k] = floo_resp_valid_i       [k][i][j];
    end : gen_router_router_wide_resp_connection_k
  end : gen_router_router_wide_resp_connection_j
end : gen_router_router_connection_i


for (genvar i = 0; i < NumTilesPerGroup; i++) begin : gen_router_router_i
  for (genvar j = 0; j < NumNarrowRemoteReqPortsPerTile; j++) begin : gen_router_narrow_req_router_j
    floo_router #(
      .NumRoutes        (mempool_pkg::NumDirections),
      .NumVirtChannels  (1            ),
      .flit_t           (floo_rd_req_t),
      .ChannelFifoDepth (mempool_pkg::NumRouterInFifoDepth), // Input buffer depth
      .OutputFifoDepth  (mempool_pkg::NumRouterOutFifoDepth), // Output buffer depth, can try to set it to 0 for -1 cycle latency
      .RouteAlgo        (XYRouting    ),
      .id_t             (group_xy_id_t),
      .NumAddrRules     (1            )
    ) i_floo_narrow_req_router (
      .clk_i,
      .rst_ni,
      .test_enable_i  (1'b0                                                                   ),
      .xy_id_i        (group_xy_id_t'(group_id_i)                                             ),
      .id_route_map_i ('0                                                                     ),
      .valid_i        ({floo_narrow_req_valid_i_trans[i][j], tcdm_master_req_valid[i][j+(1)]} ),
      .ready_o        ({floo_narrow_req_ready_o_trans[i][j], tcdm_master_req_ready[i][j+(1)]} ),
      .data_i         ({floo_narrow_req_i_trans      [i][j], floo_rd_req_to_router[i][j]}     ),
      .valid_o        ({floo_narrow_req_valid_o_trans[i][j], floo_req_from_router_before_xbar_valid[i][j+(1)]}),
      .ready_i        ({floo_narrow_req_ready_i_trans[i][j], floo_req_from_router_before_xbar_ready[i][j+(1)]}),
      .data_o         ({floo_narrow_req_o_trans      [i][j], floo_rd_req_from_router[i][j]}   )
    );
  end : gen_router_narrow_req_router_j

  for (genvar j = 0; j < NumWideRemoteReqPortsPerTile; j++) begin : gen_router_wide_req_router_j
    floo_router #(
      .NumRoutes        (mempool_pkg::NumDirections),
      .NumVirtChannels  (1            ),
      .flit_t           (floo_rdwr_req_t),
      .ChannelFifoDepth (mempool_pkg::NumRouterInFifoDepth), // Input buffer depth
      .OutputFifoDepth  (mempool_pkg::NumRouterOutFifoDepth), // Output buffer depth, can try to set it to 0 for -1 cycle latency
      .RouteAlgo        (XYRouting    ),
      .id_t             (group_xy_id_t),
      .NumAddrRules     (1            )
    ) i_floo_wide_req_router (
      .clk_i,
      .rst_ni,
      .test_enable_i  (1'b0                                                            ),
      .xy_id_i        (group_xy_id_t'(group_id_i)                                      ),
      .id_route_map_i ('0                                                              ),
      .valid_i        ({floo_wide_req_valid_i_trans[i][j], tcdm_master_req_valid[i][j+(1+NumNarrowRemoteReqPortsPerTile)]}  ),
      .ready_o        ({floo_wide_req_ready_o_trans[i][j], tcdm_master_req_ready[i][j+(1+NumNarrowRemoteReqPortsPerTile)]}  ),
      .data_i         ({floo_wide_req_i_trans      [i][j], floo_rdwr_wr_req_to_router[i][j]}    ),
      .valid_o        ({floo_wide_req_valid_o_trans[i][j], floo_req_from_router_before_xbar_valid[i][j+(1+NumNarrowRemoteReqPortsPerTile)]}),
      .ready_i        ({floo_wide_req_ready_i_trans[i][j], floo_req_from_router_before_xbar_ready[i][j+(1+NumNarrowRemoteReqPortsPerTile)]}),
      .data_o         ({floo_wide_req_o_trans      [i][j], floo_rdwr_wr_req_from_router[i][j]}  )
    );
  end : gen_router_wide_req_router_j

  for (genvar j = 1; j < NumRemoteRespPortsPerTile; j++) begin : gen_router_wide_resp_router_j
    floo_router #(
      .NumRoutes       (mempool_pkg::NumDirections),
      .NumVirtChannels (1            ),
      .flit_t          (floo_resp_t  ),
      .ChannelFifoDepth(mempool_pkg::NumRouterInFifoDepth), // Input buffer depth
      .OutputFifoDepth (mempool_pkg::NumRouterOutFifoDepth), // Output buffer depth, can try to set it to 0 for -1 cycle latency
      .RouteAlgo       (XYRouting    ),
      .id_t            (group_xy_id_t),
      .NumAddrRules    (1            )
    ) i_floo_wide_resp_router (
      .clk_i,
      .rst_ni,
      .test_enable_i  (1'b0                                                              ),
      .xy_id_i        (group_xy_id_t'(group_id_i)                                        ),
      .id_route_map_i ('0                                                                ),
      .valid_i        ({floo_resp_valid_i_trans[i][j], tcdm_slave_resp_valid[i][j]}                  ),
      .ready_o        ({floo_resp_ready_o_trans[i][j], tcdm_slave_resp_ready[i][j]}                  ),
      .data_i         ({floo_resp_i_trans[i][j],       floo_resp_to_router[i][j]}                    ),
      .valid_o        ({floo_resp_valid_o_trans[i][j], floo_resp_from_router_before_xbar_valid[i][j]}),
      .ready_i        ({floo_resp_ready_i_trans[i][j], floo_resp_from_router_before_xbar_ready[i][j]}),
      .data_o         ({floo_resp_o_trans[i][j],       floo_resp_from_router[i][j]}                  )
    );

  end : gen_router_wide_resp_router_j
end : gen_router_router_i

endmodule
