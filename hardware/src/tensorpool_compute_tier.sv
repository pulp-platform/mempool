// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Compute tier of the TensorPool 3D stack.
//
// The tier holds the NumGroups Groups and nothing else. Every port of this
// module is a die-to-die connection to the interconnect tier: there is no
// package-facing I/O on this die, no I/O ring and no C4 bump. Clock, reset,
// test and all control signals arrive through hybrid bonding terminals from
// the interconnect tier, which is the die attached to the substrate.
//
// The port list is a plain concatenation of NumGroups identical Group
// interfaces, indexed by Group, so that bump planning can be scripted from the
// index rather than from a name table.
//
// Clock and reset arrive as single nets and are distributed inside the die.
// They are deliberately NOT declared one per Group: a replicated bus does not
// buy anything in silicon, where several bond terminals can sit on the same
// clock net as a floorplan decision, and in simulation the bit selects of a
// replicated clock and a replicated reset do not necessarily resolve in the
// same delta, which shifts reset release by a cycle relative to the
// interconnect tier.
//
// Hierarchical implementation order: harden mempool_group first with all of its
// ports declared as vertical, then assemble NumGroups of them here.

`include "mempool/mempool.svh"

module tensorpool_compute_tier
  import mempool_pkg::*;
  import cf_math_pkg::idx_width;
#(
  // TCDM
  parameter addr_t                 TCDMBaseAddr  = 32'b0,
  // Boot address
  parameter logic           [31:0] BootAddr      = 32'h0000_0000,
  // Dependant parameter. DO NOT CHANGE!
  parameter int    unsigned        NumAXIMasters = NumGroups * NumAXIMastersPerGroup
) (
  // Vertical: clock, reset and test
  input  logic                                        clk_i,
  input  logic                                        rst_ni,
  input  logic                                        testmode_i,
  input  logic                                        scan_enable_i,
  // Vertical: control
  input  logic                    [NumCores-1:0]      wake_up_i,
  input  ro_cache_ctrl_t          [NumGroups-1:0]     ro_cache_ctrl_i,
  // Vertical: DMA
  input  dma_req_t                [NumGroups-1:0]     dma_req_i,
  input  logic                    [NumGroups-1:0]     dma_req_valid_i,
  output logic                    [NumGroups-1:0]     dma_req_ready_o,
  output dma_meta_t               [NumGroups-1:0]     dma_meta_o,
  // Vertical: AXI towards the interconnect tier
  output axi_tile_req_t           [NumAXIMasters-1:0] axi_mst_req_o,
  input  axi_tile_resp_t          [NumAXIMasters-1:0] axi_mst_resp_i,
`ifdef TERAPOOL
  // Vertical: requests and responses leaving the Groups
  output `STRUCT_VECT(tcdm_master_req_t,  [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0]) tcdm_master_req_o,
  output logic                            [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0]  tcdm_master_req_valid_o,
  input  logic                            [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0]  tcdm_master_req_ready_i,
  output `STRUCT_VECT(tcdm_slave_resp_t,  [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0]) tcdm_slave_resp_o,
  output logic                            [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0]  tcdm_slave_resp_valid_o,
  input  logic                            [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0]  tcdm_slave_resp_ready_i,
  // Vertical: requests and responses arriving at the Groups
  input  `STRUCT_VECT(tcdm_slave_req_t,   [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0]) tcdm_slave_req_i,
  input  logic                            [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0]  tcdm_slave_req_valid_i,
  output logic                            [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0]  tcdm_slave_req_ready_o,
  input  `STRUCT_VECT(tcdm_master_resp_t, [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0]) tcdm_master_resp_i,
  input  logic                            [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0]  tcdm_master_resp_valid_i,
  output logic                            [NumGroups-1:0][NumGroups-1:1][NumSubGroupsPerGroup-1:0][NumTilesPerSubGroup-1:0]  tcdm_master_resp_ready_o
`else
  // Vertical: requests and responses leaving the Groups
  output `STRUCT_VECT(tcdm_slave_req_t,   [NumGroups-1:0][NumGroups-1:1][NumTilesPerGroup-1:0]) tcdm_master_req_o,
  output logic                            [NumGroups-1:0][NumGroups-1:1][NumTilesPerGroup-1:0]  tcdm_master_req_valid_o,
  input  logic                            [NumGroups-1:0][NumGroups-1:1][NumTilesPerGroup-1:0]  tcdm_master_req_ready_i,
  output `STRUCT_VECT(tcdm_master_resp_t, [NumGroups-1:0][NumGroups-1:1][NumTilesPerGroup-1:0]) tcdm_slave_resp_o,
  output logic                            [NumGroups-1:0][NumGroups-1:1][NumTilesPerGroup-1:0]  tcdm_slave_resp_valid_o,
  input  logic                            [NumGroups-1:0][NumGroups-1:1][NumTilesPerGroup-1:0]  tcdm_slave_resp_ready_i,
  // Vertical: requests and responses arriving at the Groups
  input  `STRUCT_VECT(tcdm_slave_req_t,   [NumGroups-1:0][NumGroups-1:1][NumTilesPerGroup-1:0]) tcdm_slave_req_i,
  input  logic                            [NumGroups-1:0][NumGroups-1:1][NumTilesPerGroup-1:0]  tcdm_slave_req_valid_i,
  output logic                            [NumGroups-1:0][NumGroups-1:1][NumTilesPerGroup-1:0]  tcdm_slave_req_ready_o,
  input  `STRUCT_VECT(tcdm_master_resp_t, [NumGroups-1:0][NumGroups-1:1][NumTilesPerGroup-1:0]) tcdm_master_resp_i,
  input  logic                            [NumGroups-1:0][NumGroups-1:1][NumTilesPerGroup-1:0]  tcdm_master_resp_valid_i,
  output logic                            [NumGroups-1:0][NumGroups-1:1][NumTilesPerGroup-1:0]  tcdm_master_resp_ready_o
`endif
);

  /*********************
   *  Vertical inputs  *
   *********************/
  // Keep the names the Groups were wired with before the tiers were split.
  logic           [NumCores-1:0]      wake_up_q;
  ro_cache_ctrl_t [NumGroups-1:0]     ro_cache_ctrl_q;
  dma_req_t       [NumGroups-1:0]     dma_req_group_q;
  logic           [NumGroups-1:0]     dma_req_group_q_valid;
  logic           [NumGroups-1:0]     dma_req_group_q_ready;
  dma_meta_t      [NumGroups-1:0]     dma_meta;
  axi_tile_req_t  [NumAXIMasters-1:0] axi_mst_req;
  axi_tile_resp_t [NumAXIMasters-1:0] axi_mst_resp;

  assign wake_up_q             = wake_up_i;
  assign ro_cache_ctrl_q       = ro_cache_ctrl_i;
  assign dma_req_group_q       = dma_req_i;
  assign dma_req_group_q_valid = dma_req_valid_i;
  assign dma_req_ready_o       = dma_req_group_q_ready;
  assign dma_meta_o            = dma_meta;
  assign axi_mst_req_o         = axi_mst_req;
  assign axi_mst_resp          = axi_mst_resp_i;

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

      for (genvar g = 0; unsigned'(g) < NumGroups; g++) begin: gen_groups
        if (PostLayoutGr & (g == 0)) begin: gen_postly_group
          mempool_group_postlayout i_group (
            .clk_i                   (clk_i           ),
            .rst_ni                  (rst_ni          ),
            .testmode_i              (testmode_i      ),
            .scan_enable_i           (scan_enable_i   ),
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
            .dma_req_i               (dma_req_group_q[g]                                              ),
            .dma_req_valid_i         (dma_req_group_q_valid[g]                                        ),
            .dma_req_ready_o         (dma_req_group_q_ready[g]                                        ),
            // DMA status
            .dma_meta_o_backend_idle_ (dma_meta[g][1]                                                 ),
            .dma_meta_o_trans_complete_ (dma_meta[g][0]                                               ),
            // AXI interface
            .axi_mst_req_o           (axi_mst_req[g*NumAXIMastersPerGroup +: NumAXIMastersPerGroup]   ),
            .axi_mst_resp_i          (axi_mst_resp[g*NumAXIMastersPerGroup +: NumAXIMastersPerGroup]  )
          );
        end else if ((PostLayoutGr == 0) & PostLayoutSg) begin: gen_rtl_group_postly_sg
          mempool_group #(
            .TCDMBaseAddr (TCDMBaseAddr               ),
            .BootAddr     (BootAddr                   ),
            // For post-synthesis
            .GroupId      (g[idx_width(NumGroups)-1:0])
          ) i_group (
            .clk_i                   (clk_i           ),
            .rst_ni                  (rst_ni          ),
            .testmode_i              (testmode_i      ),
            .scan_enable_i           (scan_enable_i   ),
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
            .dma_req_i               (dma_req_group_q[g]                                              ),
            .dma_req_valid_i         (dma_req_group_q_valid[g]                                        ),
            .dma_req_ready_o         (dma_req_group_q_ready[g]                                        ),
            // DMA status
            .dma_meta_o              (dma_meta[g]                                                     ),
            // AXI interface
            .axi_mst_req_o           (axi_mst_req[g*NumAXIMastersPerGroup +: NumAXIMastersPerGroup]   ),
            .axi_mst_resp_i          (axi_mst_resp[g*NumAXIMastersPerGroup +: NumAXIMastersPerGroup]  )
          );
        end else begin: gen_rtl_group
          mempool_group #(
            .TCDMBaseAddr (TCDMBaseAddr         ),
            .BootAddr     (BootAddr             )
          ) i_group (
            .clk_i                   (clk_i           ),
            .rst_ni                  (rst_ni          ),
            .testmode_i              (testmode_i      ),
            .scan_enable_i           (scan_enable_i   ),
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
            .dma_req_i               (dma_req_group_q[g]                                              ),
            .dma_req_valid_i         (dma_req_group_q_valid[g]                                        ),
            .dma_req_ready_o         (dma_req_group_q_ready[g]                                        ),
            // DMA status
            .dma_meta_o              (dma_meta[g]                                                     ),
            // AXI interface
            .axi_mst_req_o           (axi_mst_req[g*NumAXIMastersPerGroup +: NumAXIMastersPerGroup]   ),
            .axi_mst_resp_i          (axi_mst_resp[g*NumAXIMastersPerGroup +: NumAXIMastersPerGroup]  )
          );
        end
      end : gen_groups

    // The Group signals are the vertical ports of this tier.
    assign tcdm_master_req_o        = tcdm_master_req;
    assign tcdm_master_req_valid_o  = tcdm_master_req_valid;
    assign tcdm_master_req_ready    = tcdm_master_req_ready_i;
    assign tcdm_slave_resp_o        = tcdm_slave_resp;
    assign tcdm_slave_resp_valid_o  = tcdm_slave_resp_valid;
    assign tcdm_slave_resp_ready    = tcdm_slave_resp_ready_i;
    assign tcdm_slave_req           = tcdm_slave_req_i;
    assign tcdm_slave_req_valid     = tcdm_slave_req_valid_i;
    assign tcdm_slave_req_ready_o   = tcdm_slave_req_ready;
    assign tcdm_master_resp         = tcdm_master_resp_i;
    assign tcdm_master_resp_valid   = tcdm_master_resp_valid_i;
    assign tcdm_master_resp_ready_o = tcdm_master_resp_ready;

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

      for (genvar g = 0; unsigned'(g) < NumGroups; g++) begin: gen_groups
        mempool_group #(
          .TCDMBaseAddr (TCDMBaseAddr         ),
          .BootAddr     (BootAddr             )
        ) i_group (
          .clk_i                   (clk_i           ),
          .rst_ni                  (rst_ni          ),
          .testmode_i              (testmode_i      ),
          .scan_enable_i           (scan_enable_i   ),
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
          .dma_req_i               (dma_req_group_q[g]                                              ),
          .dma_req_valid_i         (dma_req_group_q_valid[g]                                        ),
          .dma_req_ready_o         (dma_req_group_q_ready[g]                                        ),
          // DMA status
          .dma_meta_o              (dma_meta[g]                                                     ),
          // AXI interface
          .axi_mst_req_o           (axi_mst_req[g*NumAXIMastersPerGroup +: NumAXIMastersPerGroup] ),
          .axi_mst_resp_i          (axi_mst_resp[g*NumAXIMastersPerGroup +: NumAXIMastersPerGroup])
        );
      end : gen_groups

    // The Group signals are the vertical ports of this tier.
    assign tcdm_master_req_o        = tcdm_master_req;
    assign tcdm_master_req_valid_o  = tcdm_master_req_valid;
    assign tcdm_master_req_ready    = tcdm_master_req_ready_i;
    assign tcdm_slave_resp_o        = tcdm_slave_resp;
    assign tcdm_slave_resp_valid_o  = tcdm_slave_resp_valid;
    assign tcdm_slave_resp_ready    = tcdm_slave_resp_ready_i;
    assign tcdm_slave_req           = tcdm_slave_req_i;
    assign tcdm_slave_req_valid     = tcdm_slave_req_valid_i;
    assign tcdm_slave_req_ready_o   = tcdm_slave_req_ready;
    assign tcdm_master_resp         = tcdm_master_resp_i;
    assign tcdm_master_resp_valid   = tcdm_master_resp_valid_i;
    assign tcdm_master_resp_ready_o = tcdm_master_resp_ready;

  `endif

endmodule : tensorpool_compute_tier
