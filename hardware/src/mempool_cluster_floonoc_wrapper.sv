// Copyright 2024 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "common_cells/registers.svh"

module mempool_cluster_floonoc_wrapper
  import mempool_pkg::*;
  import cf_math_pkg::idx_width;
  import floo_pkg::*;
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
  
  floo_req_t  [NumX-2:0][NumY-1:0][NumTilesPerGroup-1:0][NumRemotePortsPerTile-1:1] pos_x_req_flit;
  logic       [NumX-2:0][NumY-1:0][NumTilesPerGroup-1:0][NumRemotePortsPerTile-1:1] pos_x_req_ready, pos_x_req_valid;
  floo_req_t  [NumX-2:0][NumY-1:0][NumTilesPerGroup-1:0][NumRemotePortsPerTile-1:1] neg_x_req_flit;
  logic       [NumX-2:0][NumY-1:0][NumTilesPerGroup-1:0][NumRemotePortsPerTile-1:1] neg_x_req_ready, neg_x_req_valid;
  floo_req_t  [NumX-1:0][NumY-2:0][NumTilesPerGroup-1:0][NumRemotePortsPerTile-1:1] pos_y_req_flit;
  logic       [NumX-1:0][NumY-2:0][NumTilesPerGroup-1:0][NumRemotePortsPerTile-1:1] pos_y_req_ready, pos_y_req_valid;
  floo_req_t  [NumX-1:0][NumY-2:0][NumTilesPerGroup-1:0][NumRemotePortsPerTile-1:1] neg_y_req_flit;
  logic       [NumX-1:0][NumY-2:0][NumTilesPerGroup-1:0][NumRemotePortsPerTile-1:1] neg_y_req_ready, neg_y_req_valid;

  floo_resp_t [NumX-2:0][NumY-1:0][NumTilesPerGroup-1:0][NumRemotePortsPerTile-1:1] pos_x_resp_flit;
  logic       [NumX-2:0][NumY-1:0][NumTilesPerGroup-1:0][NumRemotePortsPerTile-1:1] pos_x_resp_ready, pos_x_resp_valid;
  floo_resp_t [NumX-2:0][NumY-1:0][NumTilesPerGroup-1:0][NumRemotePortsPerTile-1:1] neg_x_resp_flit;
  logic       [NumX-2:0][NumY-1:0][NumTilesPerGroup-1:0][NumRemotePortsPerTile-1:1] neg_x_resp_ready, neg_x_resp_valid;
  floo_resp_t [NumX-1:0][NumY-2:0][NumTilesPerGroup-1:0][NumRemotePortsPerTile-1:1] pos_y_resp_flit;
  logic       [NumX-1:0][NumY-2:0][NumTilesPerGroup-1:0][NumRemotePortsPerTile-1:1] pos_y_resp_ready, pos_y_resp_valid;
  floo_resp_t [NumX-1:0][NumY-2:0][NumTilesPerGroup-1:0][NumRemotePortsPerTile-1:1] neg_y_resp_flit;
  logic       [NumX-1:0][NumY-2:0][NumTilesPerGroup-1:0][NumRemotePortsPerTile-1:1] neg_y_resp_ready, neg_y_resp_valid;

  for (genvar x = 0; x < NumX; x++) begin : gen_groups_x
    for (genvar y = 0; y < NumY; y++) begin : gen_groups_y
      group_xy_id_t group_id;
      assign group_id = '{x:x, y:y};

      floo_req_t  [NumDirections-2:0][NumTilesPerGroup-1:0][NumRemotePortsPerTile-1:1] in_req_flit;
      logic       [NumDirections-2:0][NumTilesPerGroup-1:0][NumRemotePortsPerTile-1:1] in_req_ready, in_req_valid;
      floo_req_t  [NumDirections-2:0][NumTilesPerGroup-1:0][NumRemotePortsPerTile-1:1] out_req_flit;
      logic       [NumDirections-2:0][NumTilesPerGroup-1:0][NumRemotePortsPerTile-1:1] out_req_ready, out_req_valid;

      floo_resp_t [NumDirections-2:0][NumTilesPerGroup-1:0][NumRemotePortsPerTile-1:1] in_resp_flit;
      logic       [NumDirections-2:0][NumTilesPerGroup-1:0][NumRemotePortsPerTile-1:1] in_resp_ready, in_resp_valid;
      floo_resp_t [NumDirections-2:0][NumTilesPerGroup-1:0][NumRemotePortsPerTile-1:1] out_resp_flit;
      logic       [NumDirections-2:0][NumTilesPerGroup-1:0][NumRemotePortsPerTile-1:1] out_resp_ready, out_resp_valid;

      always_comb begin
        in_req_flit[West:North] = '0;
        in_req_valid[West:North] = '0;
        out_req_ready[West:North] = '0;
        
        // Y
        if (y < NumY-1) begin
          in_req_flit[North]    = neg_y_req_flit[x][y];
          in_req_valid[North]   = neg_y_req_valid[x][y];
          neg_y_req_ready[x][y] = in_req_ready[North];
          pos_y_req_flit[x][y]  = out_req_flit[North];
          pos_y_req_valid[x][y] = out_req_valid[North];
          out_req_ready[North]  = pos_y_req_ready[x][y];
        end
        if (y > 0) begin
          in_req_flit[South]      = pos_y_req_flit[x][y-1];
          in_req_valid[South]     = pos_y_req_valid[x][y-1];
          pos_y_req_ready[x][y-1] = in_req_ready[South];
          neg_y_req_flit[x][y-1]  = out_req_flit[South];
          neg_y_req_valid[x][y-1] = out_req_valid[South];
          out_req_ready[South]    = neg_y_req_ready[x][y-1];
        end

        // X
        if (x < NumX-1) begin
          in_req_flit[East]     = neg_x_req_flit[x][y];
          in_req_valid[East]    = neg_x_req_valid[x][y];
          neg_x_req_ready[x][y] = in_req_ready[East];
          pos_x_req_flit[x][y]  = out_req_flit[East];
          pos_x_req_valid[x][y] = out_req_valid[East];
          out_req_ready[East]   = pos_x_req_ready[x][y];
        end
        if (x > 0) begin
          in_req_flit[West]      = pos_x_req_flit[x-1][y];
          in_req_valid[West]     = pos_x_req_valid[x-1][y];
          pos_x_req_ready[x-1][y] = in_req_ready[West];
          neg_x_req_flit[x-1][y]  = out_req_flit[West];
          neg_x_req_valid[x-1][y] = out_req_valid[West];
          out_req_ready[West]    = neg_x_req_ready[x-1][y];
        end
      end

      always_comb begin
        in_resp_flit[West:North] = '0;
        in_resp_valid[West:North] = '0;
        out_resp_ready[West:North] = '0;
        
        // Y
        if (y < NumY-1) begin
          in_resp_flit[North]    = neg_y_resp_flit[x][y];
          in_resp_valid[North]   = neg_y_resp_valid[x][y];
          neg_y_resp_ready[x][y] = in_resp_ready[North];
          pos_y_resp_flit[x][y]  = out_resp_flit[North];
          pos_y_resp_valid[x][y] = out_resp_valid[North];
          out_resp_ready[North]  = pos_y_resp_ready[x][y];
        end
        if (y > 0) begin
          in_resp_flit[South]      = pos_y_resp_flit[x][y-1];
          in_resp_valid[South]     = pos_y_resp_valid[x][y-1];
          pos_y_resp_ready[x][y-1] = in_resp_ready[South];
          neg_y_resp_flit[x][y-1]  = out_resp_flit[South];
          neg_y_resp_valid[x][y-1] = out_resp_valid[South];
          out_resp_ready[South]    = neg_y_resp_ready[x][y-1];
        end

        // X
        if (x < NumX-1) begin
          in_resp_flit[East]     = neg_x_resp_flit[x][y];
          in_resp_valid[East]    = neg_x_resp_valid[x][y];
          neg_x_resp_ready[x][y] = in_resp_ready[East];
          pos_x_resp_flit[x][y]  = out_resp_flit[East];
          pos_x_resp_valid[x][y] = out_resp_valid[East];
          out_resp_ready[East]   = pos_x_resp_ready[x][y];
        end
        if (x > 0) begin
          in_resp_flit[West]      = pos_x_resp_flit[x-1][y];
          in_resp_valid[West]     = pos_x_resp_valid[x-1][y];
          pos_x_resp_ready[x-1][y] = in_resp_ready[West];
          neg_x_resp_flit[x-1][y]  = out_resp_flit[West];
          neg_x_resp_valid[x-1][y] = out_resp_valid[West];
          out_resp_ready[West]    = neg_x_resp_ready[x-1][y];
        end
      end
      
      mempool_group_floonoc_wrapper #(
        .TCDMBaseAddr (TCDMBaseAddr         ),
        .BootAddr     (BootAddr             )
      ) i_group (
        .clk_i                   (clk_i                                                           ),
        .rst_ni                  (rst_ni                                                          ),
        .testmode_i              (testmode_i                                                      ),
        .scan_enable_i           (scan_enable_i                                                   ),
        .scan_data_i             (/* Unconnected */                                               ),
        .scan_data_o             (/* Unconnected */                                               ),
        .group_id_i              (group_id_t'(group_id)                                           ),
        // TCDM Master interfaces
        .floo_req_o              (out_req_flit                                                    ),
        .floo_req_valid_o        (out_req_valid                                                   ),
        .floo_req_ready_i        (out_req_ready                                                   ),
        .floo_resp_o             (out_resp_flit                                                   ),
        .floo_resp_valid_o       (out_resp_valid                                                  ),
        .floo_resp_ready_i       (out_resp_ready                                                  ),
        // TCDM banks interface
        .floo_req_i              (in_req_flit                                                     ),
        .floo_req_valid_i        (in_req_valid                                                    ),
        .floo_req_ready_o        (in_req_ready                                                    ),
        .floo_resp_i             (in_resp_flit                                                    ),
        .floo_resp_valid_i       (in_resp_valid                                                   ),
        .floo_resp_ready_o       (in_resp_ready                                                   ),
        .wake_up_i               (wake_up_q[g*NumCoresPerGroup +: NumCoresPerGroup]               ),
        .ro_cache_ctrl_i         (ro_cache_ctrl_q[g]                                              ),
        // DMA request
        .dma_req_i               (dma_req_group_q[g]                                              ),
        .dma_req_valid_i         (dma_req_group_q_valid[g]                                        ),
        .dma_req_ready_o         (dma_req_group_q_ready[g]                                        ),
        // DMA status
        .dma_meta_o              (dma_meta[g]                                                     ),
        // AXI interface
        .axi_mst_req_o           (axi_mst_req_o[g*NumAXIMastersPerGroup +: NumAXIMastersPerGroup] ),
        .axi_mst_resp_i          (axi_mst_resp_i[g*NumAXIMastersPerGroup +: NumAXIMastersPerGroup])
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

endmodule : mempool_cluster
