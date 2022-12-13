// Copyright 2022 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "mempool/mempool.svh"
`include "reqrsp_interface/typedef.svh"
`include "common_cells/registers.svh"

module mempool_sub_group
  import mempool_pkg::*;
  import cf_math_pkg::idx_width;
#(
  // TCDM
  parameter addr_t       TCDMBaseAddr = 32'b0,
  // Boot address
  parameter logic [31:0] BootAddr     = 32'h0000_1000
) (
  input  logic                                                                      clk_i,
  input  logic                                                                      rst_ni,
  // Scan chain
  input  logic                                                                      scan_enable_i,
  input  logic                                                                      scan_data_i,
  output logic                                                                      scan_data_o,
  // Group ID
  input  logic                            [idx_width(NumSubGroups)-1:0]             sub_group_id_i,
  // TCDM Master interfaces
  output `STRUCT_VECT(tcdm_master_req_t,  [NumGroups-1:0][NumTilesPerSubGroup-1:0]) tcdm_master_req_o,
  output logic                            [NumGroups-1:0][NumTilesPerSubGroup-1:0]  tcdm_master_req_valid_o,
  input  logic                            [NumGroups-1:0][NumTilesPerSubGroup-1:0]  tcdm_master_req_ready_i,
  input  `STRUCT_VECT(tcdm_master_resp_t, [NumGroups-1:0][NumTilesPerSubGroup-1:0]) tcdm_master_resp_i,
  input  logic                            [NumGroups-1:0][NumTilesPerSubGroup-1:0]  tcdm_master_resp_valid_i,
  output logic                            [NumGroups-1:0][NumTilesPerSubGroup-1:0]  tcdm_master_resp_ready_o,
  // TCDM Slave interfaces
  input  `STRUCT_VECT(tcdm_slave_req_t,   [NumGroups-1:0][NumTilesPerSubGroup-1:0]) tcdm_slave_req_i,
  input  logic                            [NumGroups-1:0][NumTilesPerSubGroup-1:0]  tcdm_slave_req_valid_i,
  output logic                            [NumGroups-1:0][NumTilesPerSubGroup-1:0]  tcdm_slave_req_ready_o,
  output `STRUCT_VECT(tcdm_slave_resp_t,  [NumGroups-1:0][NumTilesPerSubGroup-1:0]) tcdm_slave_resp_o,
  output logic                            [NumGroups-1:0][NumTilesPerSubGroup-1:0]  tcdm_slave_resp_valid_o,
  input  logic                            [NumGroups-1:0][NumTilesPerSubGroup-1:0]  tcdm_slave_resp_ready_i,
  // TCDM DMA interfaces
  input  `STRUCT_PORT(tcdm_dma_req_t)     [NumTilesPerSubGroup-1:0]                 tcdm_dma_req_i,
  input  logic                            [NumTilesPerSubGroup-1:0]                 tcdm_dma_req_valid_i,
  output logic                            [NumTilesPerSubGroup-1:0]                 tcdm_dma_req_ready_o,
  output `STRUCT_PORT(tcdm_dma_resp_t)    [NumTilesPerSubGroup-1:0]                 tcdm_dma_resp_o,
  output logic                            [NumTilesPerSubGroup-1:0]                 tcdm_dma_resp_valid_o,
  input  logic                            [NumTilesPerSubGroup-1:0]                 tcdm_dma_resp_ready_i,
  // AXI Interface
  output `STRUCT_PORT(axi_tile_req_t)     [NumTilesPerSubGroup-1:0]                 axi_mst_req_o,
  input  `STRUCT_PORT(axi_tile_resp_t)    [NumTilesPerSubGroup-1:0]                 axi_mst_resp_i,
  // Wake up interface
  input  logic                            [NumCoresPerSubGroup-1:0]                 wake_up_i
);

  /*****************
   *  Definitions  *
   *****************/

  typedef logic [idx_width(NumTiles)-1:0] tile_id_t;

  /*********************
   *  Control Signals  *
   *********************/
  logic [NumCoresPerSubGroup-1:0] wake_up_q;
  `FF(wake_up_q, wake_up_i, '0, clk_i, rst_ni);

  /**********************
   *  Ports to structs  *
   **********************/

  // The ports might be structs flattened to vectors. To access the structs'
  // internal signals, assign the flattened vectors back to structs.
  tcdm_slave_req_t   [NumGroups-1:0][NumTilesPerSubGroup-1:0] tcdm_master_req_s;
  tcdm_master_resp_t [NumGroups-1:0][NumTilesPerSubGroup-1:0] tcdm_slave_resp_s;

  /***********
   *  Tiles  *
   ***********/

  // TCDM interfaces
  tcdm_master_req_t  [NumGroups-1:0][NumTilesPerSubGroup-1:0] tcdm_master_req;
  logic              [NumGroups-1:0][NumTilesPerSubGroup-1:0] tcdm_master_req_valid;
  logic              [NumGroups-1:0][NumTilesPerSubGroup-1:0] tcdm_master_req_ready;
  tcdm_slave_req_t   [NumGroups-1:0][NumTilesPerSubGroup-1:0] tcdm_slave_req;
  logic              [NumGroups-1:0][NumTilesPerSubGroup-1:0] tcdm_slave_req_valid;
  logic              [NumGroups-1:0][NumTilesPerSubGroup-1:0] tcdm_slave_req_ready;
  tcdm_master_resp_t [NumGroups-1:0][NumTilesPerSubGroup-1:0] tcdm_master_resp;
  logic              [NumGroups-1:0][NumTilesPerSubGroup-1:0] tcdm_master_resp_valid;
  logic              [NumGroups-1:0][NumTilesPerSubGroup-1:0] tcdm_master_resp_ready;
  tcdm_slave_resp_t  [NumGroups-1:0][NumTilesPerSubGroup-1:0] tcdm_slave_resp;
  logic              [NumGroups-1:0][NumTilesPerSubGroup-1:0] tcdm_slave_resp_valid;
  logic              [NumGroups-1:0][NumTilesPerSubGroup-1:0] tcdm_slave_resp_ready;
  // DMA interfaces
  tcdm_dma_req_t  [NumTilesPerSubGroup-1:0] tcdm_dma_req;
  logic           [NumTilesPerSubGroup-1:0] tcdm_dma_req_valid;
  logic           [NumTilesPerSubGroup-1:0] tcdm_dma_req_ready;
  tcdm_dma_resp_t [NumTilesPerSubGroup-1:0] tcdm_dma_resp;
  logic           [NumTilesPerSubGroup-1:0] tcdm_dma_resp_valid;
  logic           [NumTilesPerSubGroup-1:0] tcdm_dma_resp_ready;

  // AXI interfaces
  axi_tile_req_t  [NumTilesPerSubGroup-1:0] axi_tile_req;
  axi_tile_resp_t [NumTilesPerSubGroup-1:0] axi_tile_resp;
  assign axi_mst_req_o = axi_tile_req;
  assign axi_tile_resp = axi_mst_resp_i;

  for (genvar t = 0; unsigned'(t) < NumTilesPerSubGroup; t++) begin: gen_tiles
    tile_id_t id;
    assign id = (sub_group_id_i << $clog2(NumTilesPerSubGroup)) | t[idx_width(NumTilesPerSubGroup)-1:0];

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
      .tcdm_dma_req_i          (tcdm_dma_req[t]                                ),
      .tcdm_dma_req_valid_i    (tcdm_dma_req_valid[t]                          ),
      .tcdm_dma_req_ready_o    (tcdm_dma_req_ready[t]                          ),
      .tcdm_dma_resp_o         (tcdm_dma_resp[t]                               ),
      .tcdm_dma_resp_valid_o   (tcdm_dma_resp_valid[t]                         ),
      .tcdm_dma_resp_ready_i   (tcdm_dma_resp_ready[t]                         ),
      // AXI interface
      .axi_mst_req_o           (axi_tile_req[t]                                ),
      .axi_mst_resp_i          (axi_tile_resp[t]                               ),
      // Wake up interface
      .wake_up_i               (wake_up_q[t*NumCoresPerTile +: NumCoresPerTile])
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

  /***************
   *  Registers  *
   ***************/
`ifdef NumTilesPerSubGroup != 1
  // Break paths between request and response with registers
  for (genvar h = 0; unsigned'(h) < NumGroups; h++) begin: gen_tcdm_registers_g
  	for (genvar t = 0; unsigned'(t) < NumTilesPerSubGroup; t++) begin: gen_tcdm_registers_t
  	  //TCDM	
      spill_register #(
        .T(tcdm_master_req_t)
      ) i_tcdm_master_req_register (
        .clk_i  (clk_i                         ),
        .rst_ni (rst_ni                        ),
        .data_i (tcdm_master_req[h][t]         ),
        .valid_i(tcdm_master_req_valid[h][t]   ),
        .ready_o(tcdm_master_req_ready[h][t]   ),
        .data_o (tcdm_master_req_o[h][t]       ),
        .valid_o(tcdm_master_req_valid_o[h][t] ),
        .ready_i(tcdm_master_req_ready_i[h][t] )
      );

      fall_through_register #(
        .T(tcdm_master_resp_t)
      ) i_tcdm_master_resp_register (
        .clk_i     (clk_i                          ),
        .rst_ni    (rst_ni                         ),
        .clr_i     (1'b0                           ),
        .testmode_i(1'b0                           ),
        .data_i    (tcdm_master_resp_i[h][t]       ),
        .valid_i   (tcdm_master_resp_valid_i[h][t] ),
        .ready_o   (tcdm_master_resp_ready_o[h][t] ),
        .data_o    (tcdm_master_resp[h][t]         ),
        .valid_o   (tcdm_master_resp_valid[h][t]   ),
        .ready_i   (tcdm_master_resp_ready[h][t]   )
      );

      fall_through_register #(
        .T(tcdm_slave_req_t)
      ) i_tcdm_slave_req_register (
        .clk_i     (clk_i                        ),
        .rst_ni    (rst_ni                       ),
        .clr_i     (1'b0                         ),
        .testmode_i(1'b0                         ),
        .data_i    (tcdm_slave_req_i[h][t]       ),
        .valid_i   (tcdm_slave_req_valid_i[h][t] ),
        .ready_o   (tcdm_slave_req_ready_o[h][t] ),
        .data_o    (tcdm_slave_req[h][t]         ),
        .valid_o   (tcdm_slave_req_valid[h][t]   ),
        .ready_i   (tcdm_slave_req_ready[h][t]   )
      );

      spill_register #(
        .T(tcdm_slave_resp_t)
      ) i_tcdm_slave_resp_register (
        .clk_i  (clk_i                         ),
        .rst_ni (rst_ni                        ),
        .data_i (tcdm_slave_resp[h][t]         ),
        .valid_i(tcdm_slave_resp_valid[h][t]   ),
        .ready_o(tcdm_slave_resp_ready[h][t]   ),
        .data_o (tcdm_slave_resp_o[h][t]       ),
        .valid_o(tcdm_slave_resp_valid_o[h][t] ),
        .ready_i(tcdm_slave_resp_ready_i[h][t] )
      );
    end: gen_tcdm_registers_t
  end: gen_tcdm_registers_g

  //TCDM DMA
  for (genvar t = 0; unsigned'(t) < NumTilesPerSubGroup; t++) begin: gen_tcdm_dma_registers
    spill_register #(
      .T(tcdm_dma_req_t)
    ) i_tcdm_dma_req_register (
      .clk_i  (clk_i                   ),
      .rst_ni (rst_ni                  ),
      .data_i (tcdm_dma_req_i[t]       ),
      .valid_i(tcdm_dma_req_valid_i[t] ),
      .ready_o(tcdm_dma_req_ready_o[t] ),
      .data_o (tcdm_dma_req[t]         ),
      .valid_o(tcdm_dma_req_valid[t]   ),
      .ready_i(tcdm_dma_req_ready[t]   )
    );  	

    spill_register #(
      .T(tcdm_dma_resp_t)
    ) i_tcdm_dma_resp_register (
      .clk_i  (clk_i                    ),
      .rst_ni (rst_ni                   ),
      .data_i (tcdm_dma_resp[t]         ),
      .valid_i(tcdm_dma_resp_valid[t]   ),
      .ready_o(tcdm_dma_resp_ready[t]   ),
      .data_o (tcdm_dma_resp_o[t]       ),
      .valid_o(tcdm_dma_resp_valid_o[t] ),
      .ready_i(tcdm_dma_resp_ready_i[t] )
    );
  end: gen_tcdm_dma_registers*/
`else
  // Direct connection to group level
  // TCDM
  assign tcdm_master_req_o = tcdm_master_req;
  assign tcdm_master_req_valid_o = tcdm_master_req_valid;
  assign tcdm_master_req_ready = tcdm_master_req_ready_i;
  assign tcdm_slave_req = tcdm_slave_req_i;
  assign tcdm_slave_req_valid = tcdm_slave_req_valid_i;
  assign tcdm_slave_req_ready_o = tcdm_slave_req_ready;
  assign tcdm_master_resp = tcdm_master_resp_i;
  assign tcdm_master_resp_valid = tcdm_master_resp_valid_i;
  assign tcdm_master_resp_ready_o = tcdm_master_resp_ready;
  assign tcdm_slave_resp_o = tcdm_slave_resp;
  assign tcdm_slave_resp_valid_o = tcdm_slave_resp_valid;
  assign tcdm_slave_resp_ready = tcdm_slave_resp_ready_i;

  //TCDM DMA
  assign tcdm_dma_req = tcdm_dma_req_i;
  assign tcdm_dma_req_valid = tcdm_dma_req_valid_i;
  assign tcdm_dma_req_ready_o = tcdm_dma_req_ready;
  assign tcdm_dma_resp_o = tcdm_dma_resp;
  assign tcdm_dma_resp_valid_o = tcdm_dma_resp_valid;
  assign tcdm_dma_resp_ready = tcdm_dma_resp_ready_i;
`endif

endmodule : mempool_sub_group
