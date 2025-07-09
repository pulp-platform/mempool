// Copyright 2025 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`ifndef TB_NOC_PROFILING_SVH_
`define TB_NOC_PROFILING_SVH_

`ifndef TARGET_SYNTHESIS
`ifndef TARGET_VERILATOR
  logic [63:0] cycle_q;
  always_ff @(posedge clk or negedge rst_n) begin
    if(~rst_n) begin
      cycle_q   <= '0;
    end else begin
      cycle_q   <= cycle_q + 64'd1;
    end
  end

`ifdef NOC_PROFILING
  string  app, log_path, dump_time;
  integer retval;
  // File handles and filenames for various profiling logs
  int     f_2, f_3, f_4, f_5;
  int     f_final_2, f_final_3, f_final_4, f_final_5;
  string  fn_2, fn_3, fn_4, fn_5;
  string  fn_final_2, fn_final_3, fn_final_4, fn_final_5;
  // Input/output log file descriptors
  int     req_floo_input_log_fd, resp_floo_input_log_fd;

  initial begin
    // Read APP name from command line argument
    void'($value$plusargs("APP=%s", app));
    // Set profiling output path
    $sformat(log_path, "noc_profiling");
    // Create log directory
    retval = $system({"mkdir -p ", log_path});
    // Open input/output log files
    req_floo_input_log_fd  = $fopen($sformatf("%s/req_floo_input.log",  log_path), "w");
    resp_floo_input_log_fd = $fopen($sformatf("%s/resp_floo_input.log", log_path), "w");
  end

  // ------------------------------------------------------------
  // Profiling structures
  // ------------------------------------------------------------

  tile_level_profile_t            tile_level_profile_q              [NumGroups-1:0][NumTilesPerGroup-1:0];
  group_level_profile_t           group_level_profile_q             [NumGroups-1:0];

  router_level_profile_t          router_level_profile_req_q        [NumGroups-1:0][NumTilesPerGroup-1:0][NumWideRemoteReqPortsPerTile-1:0];
  router_local_req_port_profile_t router_local_req_port_profile_q   [NumGroups-1:0][NumTilesPerGroup-1:0][NumWideRemoteReqPortsPerTile-1:0];

  router_level_profile_t          router_level_profile_resp_q       [NumGroups-1:0][NumTilesPerGroup-1:0][NumRemoteRespPortsPerTile-2:0];
  router_local_resp_port_profile_t router_local_resp_port_profile_q [NumGroups-1:0][NumTilesPerGroup-1:0][NumRemoteRespPortsPerTile-2:0];

  // ------------------------------------------------------------
  // Tile-level profiling: counts valid and handshake cycles
  // ------------------------------------------------------------

  generate
    for (genvar g = 0; g < NumGroups; g++) begin : gen_group
      for (genvar t = 0; t < NumTilesPerGroup; t++) begin : gen_tile
        always_ff @(posedge clk or negedge rst_n) begin
          if (!rst_n) begin
            for (int p = 0; p < (NumRemoteReqPortsPerTile - 1); p++) begin
              tile_level_profile_q[g][t].req_vld_cyc_num[p] <= '0;
              tile_level_profile_q[g][t].req_hsk_cyc_num[p] <= '0;
            end
          end else begin
            for (int p = 0; p < (NumRemoteReqPortsPerTile - 1); p++) begin
              tile_level_profile_q[g][t].req_vld_cyc_num[p] <=
                  tile_level_profile_q[g][t].req_vld_cyc_num[p] +
                  $countones(
                    dut.i_mempool_cluster
                      .gen_groups_x[g / NumY]
                      .gen_groups_y[g % NumY]
                      .i_group
                      .i_mempool_group
                      .gen_tiles[t]
                      .i_tile
                      .tcdm_master_req_valid_o[p + 1]
                  );

              tile_level_profile_q[g][t].req_hsk_cyc_num[p] <=
                  tile_level_profile_q[g][t].req_hsk_cyc_num[p] +
                  $countones(
                    dut.i_mempool_cluster
                      .gen_groups_x[g / NumY]
                      .gen_groups_y[g % NumY]
                      .i_group
                      .i_mempool_group
                      .gen_tiles[t]
                      .i_tile
                      .tcdm_master_req_valid_o[p + 1] &
                    dut.i_mempool_cluster
                      .gen_groups_x[g / NumY]
                      .gen_groups_y[g % NumY]
                      .i_group
                      .i_mempool_group
                      .gen_tiles[t]
                      .i_tile
                      .tcdm_master_req_ready_i[p + 1]
                  );
            end
          end
        end
      end
    end
  endgenerate

  // ------------------------------------------------------------
  // Group-level profiling signals
  // ------------------------------------------------------------

  // Count of requests targeting the same bank from multiple tiles
  logic [NumGroups-1:0]
        [NumTilesPerGroup * NumBanksPerTile - 1:0]
        [$clog2(NumTilesPerGroup * (NumRemoteReqPortsPerTile - 1)) : 0]
        group_xbar_req_to_same_bank_count;

  // Count of bank access conflicts from multiple requesters
  logic [NumGroups-1:0]
        [NumTilesPerGroup * NumBanksPerTile - 1:0]
        [$clog2(NumTilesPerGroup * (NumRemoteReqPortsPerTile - 1)) : 0]
        group_xbar_req_to_same_bank_conflict_count;

  // Sum of conflict counts across all banks in a group
  logic [NumGroups-1:0]
        [$clog2(NumTilesPerGroup * (NumRemoteReqPortsPerTile - 1)) : 0]
        group_xbar_req_to_same_bank_conflict_count_sum;

  // Per-port valid signal for incoming requests to TCDM crossbar
  logic [NumX-1:0]
        [NumY-1:0]
        [NumRemoteReqPortsPerTile - 2:0]
        [NumTilesPerGroup-1:0]
        tcdm_slave_req_valid;

  // Per-port target address for incoming requests to TCDM crossbar
  logic [NumX-1:0]
        [NumY-1:0]
        [NumRemoteReqPortsPerTile - 2:0]
        [NumTilesPerGroup-1:0]
        [idx_width(NumTilesPerGroup) + idx_width(NumBanksPerTile) - 1 : 0]
        tcdm_slave_req_tgt_addr;

  // ------------------------------------------------------------
  // Capture TCDM slave port request valid & address per tile/port
  // ------------------------------------------------------------
  generate
    for (genvar x_dim = 0; x_dim < NumX; x_dim++) begin : gen_x
      for (genvar y_dim = 0; y_dim < NumY; y_dim++) begin : gen_y
        for (genvar p = 0; p < (NumRemoteReqPortsPerTile - 1); p++) begin : gen_port
          for (genvar t_i = 0; t_i < NumTilesPerGroup; t_i++) begin : gen_tile
            assign tcdm_slave_req_valid[x_dim][y_dim][p][t_i] =
                dut.i_mempool_cluster
                  .gen_groups_x[x_dim]
                  .gen_groups_y[y_dim]
                  .i_group
                  .floo_req_from_router_before_xbar_valid_per_port[p + 1][t_i];

            assign tcdm_slave_req_tgt_addr[x_dim][y_dim][p][t_i] =
                dut.i_mempool_cluster
                  .gen_groups_x[x_dim]
                  .gen_groups_y[y_dim]
                  .i_group
                  .floo_req_from_router[t_i][p + 1]
                  .hdr.tgt_addr[
                    idx_width(NumTilesPerGroup) + idx_width(NumBanksPerTile) - 1 : 0
                  ];
          end
        end
      end
    end
  endgenerate

  always_comb begin
    group_xbar_req_to_same_bank_count = '0;

    for (int g = 0; g < NumGroups; g++) begin
      for (int p = 0; p < (NumRemoteReqPortsPerTile - 1); p++) begin
        for (int t_i = 0; t_i < NumTilesPerGroup; t_i++) begin
          // If source port from router is valid
          if (tcdm_slave_req_valid[g / NumY][g % NumY][p][t_i]) begin
            // Then destination port count +1
            group_xbar_req_to_same_bank_count[g][
              tcdm_slave_req_tgt_addr[g / NumY][g % NumY][p][t_i]
            ] += 1;
          end
        end
      end
    end
  end

  always_comb begin
    group_xbar_req_to_same_bank_conflict_count     = '0;
    group_xbar_req_to_same_bank_conflict_count_sum = '0;

    for (int g = 0; g < NumGroups; g++) begin
      for (int b = 0; b < NumTilesPerGroup * NumBanksPerTile; b++) begin
        if (group_xbar_req_to_same_bank_count[g][b] > 0) begin
          // Minus the one that is not a conflict
          group_xbar_req_to_same_bank_conflict_count[g][b] =
              group_xbar_req_to_same_bank_count[g][b] - 1;
        end

        group_xbar_req_to_same_bank_conflict_count_sum[g] +=
            group_xbar_req_to_same_bank_conflict_count[g][b];
      end
    end
  end

  generate
    for (genvar g = 0; g < NumGroups; g++) begin : gen_group_level_profile
      always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
          for (int p = 0; p < (NumRemoteReqPortsPerTile - 1); p++) begin
            group_level_profile_q[g].req_vld_cyc_num[p] = '0;
            group_level_profile_q[g].req_hsk_cyc_num[p] = '0;
          end
          group_level_profile_q[g].req_vld_cyc_more_than_one_hit_same_bank_num = '0;
        end else begin
          for (int p = 0; p < (NumRemoteReqPortsPerTile - 1); p++) begin
            group_level_profile_q[g].req_vld_cyc_num[p] +=
                $countones(
                  dut.i_mempool_cluster
                    .gen_groups_x[g / NumY]
                    .gen_groups_y[g % NumY]
                    .i_group
                    .floo_req_from_router_before_xbar_valid_per_port[p + 1]
                    [NumTilesPerGroup - 1 : 0]
                );

            group_level_profile_q[g].req_hsk_cyc_num[p] +=
                $countones(
                  dut.i_mempool_cluster
                    .gen_groups_x[g / NumY]
                    .gen_groups_y[g % NumY]
                    .i_group
                    .floo_req_from_router_before_xbar_valid_per_port[p + 1]
                    [NumTilesPerGroup - 1 : 0] &

                  dut.i_mempool_cluster
                    .gen_groups_x[g / NumY]
                    .gen_groups_y[g % NumY]
                    .i_group
                    .floo_req_from_router_before_xbar_ready_per_port[p + 1]
                    [NumTilesPerGroup - 1 : 0]
                );
          end

          group_level_profile_q[g].req_vld_cyc_more_than_one_hit_same_bank_num +=
              group_xbar_req_to_same_bank_conflict_count_sum[g];
        end
      end
    end
  endgenerate

  // router level profiling
  generate
    for (genvar g = 0; g < NumGroups; g++) begin : gen_router_profile_per_group
      for (genvar t = 0; t < NumTilesPerGroup; t++) begin : gen_router_profile_per_tile
        for (genvar p = 0; p < (NumRemoteReqPortsPerTile - 1); p++) begin : gen_req_router_profile_per_remote_port
          if (p < NumNarrowRemoteReqPortsPerTile) begin
            always_ff @(posedge clk or negedge rst_n) begin
              if (!rst_n) begin
                router_local_req_port_profile_q[g][t][p].read_req_num  = '0;
                router_local_req_port_profile_q[g][t][p].write_req_num = '0;

                for (int router_p = 0; router_p < 4; router_p++) begin
                  router_level_profile_req_q[g][t][p].in_vld_cyc_num[router_p]  = '0;
                  router_level_profile_req_q[g][t][p].in_hsk_cyc_num[router_p]  = '0;
                  router_level_profile_req_q[g][t][p].out_vld_cyc_num[router_p] = '0;
                  router_level_profile_req_q[g][t][p].out_hsk_cyc_num[router_p] = '0;
                end
              end else begin
                router_local_req_port_profile_q[g][t][p].read_req_num +=
                    $countones(
                      (|(
                        dut.i_mempool_cluster
                          .gen_groups_x[g / NumY]
                          .gen_groups_y[g % NumY]
                          .i_group
                          .gen_router_router_i[t]
                          .gen_router_narrow_req_router_j[p]
                          .i_floo_narrow_req_router.valid_i[0] &

                        dut.i_mempool_cluster
                          .gen_groups_x[g / NumY]
                          .gen_groups_y[g % NumY]
                          .i_group
                          .gen_router_router_i[t]
                          .gen_router_narrow_req_router_j[p]
                          .i_floo_narrow_req_router.ready_i[0]
                      )) & ~dut.i_mempool_cluster
                            .gen_groups_x[g / NumY]
                            .gen_groups_y[g % NumY]
                            .i_group
                            .gen_router_router_i[t]
                            .gen_router_narrow_req_router_j[p]
                            .i_floo_narrow_req_router.data_i[0][0].payload.wen
                    );

                for (int router_p = 0; router_p < 4; router_p++) begin
                  // narrow req router

                  router_level_profile_req_q[g][t][p].in_vld_cyc_num[router_p] +=
                      $countones(
                        |dut.i_mempool_cluster
                          .gen_groups_x[g / NumY]
                          .gen_groups_y[g % NumY]
                          .i_group
                          .gen_router_router_i[t]
                          .gen_router_narrow_req_router_j[p]
                          .i_floo_narrow_req_router.valid_i[router_p + 1]
                      );

                  router_level_profile_req_q[g][t][p].in_hsk_cyc_num[router_p] +=
                      $countones(
                        |(
                          dut.i_mempool_cluster
                            .gen_groups_x[g / NumY]
                            .gen_groups_y[g % NumY]
                            .i_group
                            .gen_router_router_i[t]
                            .gen_router_narrow_req_router_j[p]
                            .i_floo_narrow_req_router.valid_i[router_p + 1] &

                          dut.i_mempool_cluster
                            .gen_groups_x[g / NumY]
                            .gen_groups_y[g % NumY]
                            .i_group
                            .gen_router_router_i[t]
                            .gen_router_narrow_req_router_j[p]
                            .i_floo_narrow_req_router.ready_o[router_p + 1]
                        )
                      );

                  router_level_profile_req_q[g][t][p].out_vld_cyc_num[router_p] +=
                      $countones(
                        |dut.i_mempool_cluster
                          .gen_groups_x[g / NumY]
                          .gen_groups_y[g % NumY]
                          .i_group
                          .gen_router_router_i[t]
                          .gen_router_narrow_req_router_j[p]
                          .i_floo_narrow_req_router.valid_o[router_p + 1]
                      );

                  router_level_profile_req_q[g][t][p].out_hsk_cyc_num[router_p] +=
                      $countones(
                        |(
                          dut.i_mempool_cluster
                            .gen_groups_x[g / NumY]
                            .gen_groups_y[g % NumY]
                            .i_group
                            .gen_router_router_i[t]
                            .gen_router_narrow_req_router_j[p]
                            .i_floo_narrow_req_router.valid_o[router_p + 1] &

                          dut.i_mempool_cluster
                            .gen_groups_x[g / NumY]
                            .gen_groups_y[g % NumY]
                            .i_group
                            .gen_router_router_i[t]
                            .gen_router_narrow_req_router_j[p]
                            .i_floo_narrow_req_router.ready_i[router_p + 1]
                        )
                      );
                end
              end
            end
          end
          else begin
            always_ff @(posedge clk or negedge rst_n) begin
              if (!rst_n) begin
                router_local_req_port_profile_q[g][t][p].read_req_num  = '0;
                router_local_req_port_profile_q[g][t][p].write_req_num = '0;

                for (int router_p = 0; router_p < 4; router_p++) begin
                  router_level_profile_req_q[g][t][p].in_vld_cyc_num[router_p]  = '0;
                  router_level_profile_req_q[g][t][p].in_hsk_cyc_num[router_p]  = '0;
                  router_level_profile_req_q[g][t][p].out_vld_cyc_num[router_p] = '0;
                  router_level_profile_req_q[g][t][p].out_hsk_cyc_num[router_p] = '0;
                end
              end else begin
                router_local_req_port_profile_q[g][t][p].read_req_num +=
                    $countones(
                      (|(
                        dut.i_mempool_cluster
                          .gen_groups_x[g / NumY]
                          .gen_groups_y[g % NumY]
                          .i_group
                          .gen_router_router_i[t]
                          .gen_router_wide_req_router_j[p - NumNarrowRemoteReqPortsPerTile]
                          .i_floo_wide_req_router.valid_i[0] &

                        dut.i_mempool_cluster
                          .gen_groups_x[g / NumY]
                          .gen_groups_y[g % NumY]
                          .i_group
                          .gen_router_router_i[t]
                          .gen_router_wide_req_router_j[p - NumNarrowRemoteReqPortsPerTile]
                          .i_floo_wide_req_router.ready_i[0]
                      )) & ~dut.i_mempool_cluster
                            .gen_groups_x[g / NumY]
                            .gen_groups_y[g % NumY]
                            .i_group
                            .gen_router_router_i[t]
                            .gen_router_wide_req_router_j[p - NumNarrowRemoteReqPortsPerTile]
                            .i_floo_wide_req_router.data_i[0][0].payload.wen
                    );

                router_local_req_port_profile_q[g][t][p].write_req_num +=
                    $countones(
                      (|(
                        dut.i_mempool_cluster
                          .gen_groups_x[g / NumY]
                          .gen_groups_y[g % NumY]
                          .i_group
                          .gen_router_router_i[t]
                          .gen_router_wide_req_router_j[p - NumNarrowRemoteReqPortsPerTile]
                          .i_floo_wide_req_router.valid_i[0] &

                        dut.i_mempool_cluster
                          .gen_groups_x[g / NumY]
                          .gen_groups_y[g % NumY]
                          .i_group
                          .gen_router_router_i[t]
                          .gen_router_wide_req_router_j[p - NumNarrowRemoteReqPortsPerTile]
                          .i_floo_wide_req_router.ready_i[0]
                      )) & dut.i_mempool_cluster
                            .gen_groups_x[g / NumY]
                            .gen_groups_y[g % NumY]
                            .i_group
                            .gen_router_router_i[t]
                            .gen_router_wide_req_router_j[p - NumNarrowRemoteReqPortsPerTile]
                            .i_floo_wide_req_router.data_i[0][0].payload.wen
                    );

                for (int router_p = 0; router_p < 4; router_p++) begin
                  // wide req router

                  router_level_profile_req_q[g][t][p].in_vld_cyc_num[router_p] +=
                      $countones(
                        |dut.i_mempool_cluster
                          .gen_groups_x[g / NumY]
                          .gen_groups_y[g % NumY]
                          .i_group
                          .gen_router_router_i[t]
                          .gen_router_wide_req_router_j[p - NumNarrowRemoteReqPortsPerTile]
                          .i_floo_wide_req_router.valid_i[router_p + 1]
                      );

                  router_level_profile_req_q[g][t][p].in_hsk_cyc_num[router_p] +=
                      $countones(
                        |(
                          dut.i_mempool_cluster
                            .gen_groups_x[g / NumY]
                            .gen_groups_y[g % NumY]
                            .i_group
                            .gen_router_router_i[t]
                            .gen_router_wide_req_router_j[p - NumNarrowRemoteReqPortsPerTile]
                            .i_floo_wide_req_router.valid_i[router_p + 1] &

                          dut.i_mempool_cluster
                            .gen_groups_x[g / NumY]
                            .gen_groups_y[g % NumY]
                            .i_group
                            .gen_router_router_i[t]
                            .gen_router_wide_req_router_j[p - NumNarrowRemoteReqPortsPerTile]
                            .i_floo_wide_req_router.ready_o[router_p + 1]
                        )
                      );

                  router_level_profile_req_q[g][t][p].out_vld_cyc_num[router_p] +=
                      $countones(
                        |dut.i_mempool_cluster
                          .gen_groups_x[g / NumY]
                          .gen_groups_y[g % NumY]
                          .i_group
                          .gen_router_router_i[t]
                          .gen_router_wide_req_router_j[p - NumNarrowRemoteReqPortsPerTile]
                          .i_floo_wide_req_router.valid_o[router_p + 1]
                      );

                  router_level_profile_req_q[g][t][p].out_hsk_cyc_num[router_p] +=
                      $countones(
                        |(
                          dut.i_mempool_cluster
                            .gen_groups_x[g / NumY]
                            .gen_groups_y[g % NumY]
                            .i_group
                            .gen_router_router_i[t]
                            .gen_router_wide_req_router_j[p - NumNarrowRemoteReqPortsPerTile]
                            .i_floo_wide_req_router.valid_o[router_p + 1] &

                          dut.i_mempool_cluster
                            .gen_groups_x[g / NumY]
                            .gen_groups_y[g % NumY]
                            .i_group
                            .gen_router_router_i[t]
                            .gen_router_wide_req_router_j[p - NumNarrowRemoteReqPortsPerTile]
                            .i_floo_wide_req_router.ready_i[router_p + 1]
                        )
                      );
                end
              end
            end
          end
        end
        for (genvar p = 0; p < (NumRemoteRespPortsPerTile - 1); p++) begin : gen_resp_router_profile_per_remote_port
          always_ff @(posedge clk or negedge rst_n) begin
            if (!rst_n) begin
              router_local_resp_port_profile_q[g][t][p].req_num = '0;

              for (int router_p = 0; router_p < 4; router_p++) begin
                router_level_profile_resp_q[g][t][p].in_vld_cyc_num[router_p]  = '0;
                router_level_profile_resp_q[g][t][p].in_hsk_cyc_num[router_p]  = '0;
                router_level_profile_resp_q[g][t][p].out_vld_cyc_num[router_p] = '0;
                router_level_profile_resp_q[g][t][p].out_hsk_cyc_num[router_p] = '0;
              end
            end else begin
              router_local_resp_port_profile_q[g][t][p].req_num +=
                  $countones(
                    |(
                      dut.i_mempool_cluster
                        .gen_groups_x[g / NumY]
                        .gen_groups_y[g % NumY]
                        .i_group
                        .gen_router_router_i[t]
                        .gen_router_wide_resp_router_j[p + 1]
                        .i_floo_wide_resp_router.valid_i[0] &

                      dut.i_mempool_cluster
                        .gen_groups_x[g / NumY]
                        .gen_groups_y[g % NumY]
                        .i_group
                        .gen_router_router_i[t]
                        .gen_router_wide_resp_router_j[p + 1]
                        .i_floo_wide_resp_router.ready_i[0]
                    )
                  );

              for (int router_p = 0; router_p < 4; router_p++) begin
                // resp router

                router_level_profile_resp_q[g][t][p].in_vld_cyc_num[router_p] +=
                    $countones(
                      |dut.i_mempool_cluster
                        .gen_groups_x[g / NumY]
                        .gen_groups_y[g % NumY]
                        .i_group
                        .gen_router_router_i[t]
                        .gen_router_wide_resp_router_j[p + 1]
                        .i_floo_wide_resp_router.valid_i[router_p + 1]
                    );

                router_level_profile_resp_q[g][t][p].in_hsk_cyc_num[router_p] +=
                    $countones(
                      |(
                        dut.i_mempool_cluster
                          .gen_groups_x[g / NumY]
                          .gen_groups_y[g % NumY]
                          .i_group
                          .gen_router_router_i[t]
                          .gen_router_wide_resp_router_j[p + 1]
                          .i_floo_wide_resp_router.valid_i[router_p + 1] &

                        dut.i_mempool_cluster
                          .gen_groups_x[g / NumY]
                          .gen_groups_y[g % NumY]
                          .i_group
                          .gen_router_router_i[t]
                          .gen_router_wide_resp_router_j[p + 1]
                          .i_floo_wide_resp_router.ready_o[router_p + 1]
                      )
                    );

                router_level_profile_resp_q[g][t][p].out_vld_cyc_num[router_p] +=
                    $countones(
                      |dut.i_mempool_cluster
                        .gen_groups_x[g / NumY]
                        .gen_groups_y[g % NumY]
                        .i_group
                        .gen_router_router_i[t]
                        .gen_router_wide_resp_router_j[p + 1]
                        .i_floo_wide_resp_router.valid_o[router_p + 1]
                    );

                router_level_profile_resp_q[g][t][p].out_hsk_cyc_num[router_p] +=
                    $countones(
                      |(
                        dut.i_mempool_cluster
                          .gen_groups_x[g / NumY]
                          .gen_groups_y[g % NumY]
                          .i_group
                          .gen_router_router_i[t]
                          .gen_router_wide_resp_router_j[p + 1]
                          .i_floo_wide_resp_router.valid_o[router_p + 1] &

                        dut.i_mempool_cluster
                          .gen_groups_x[g / NumY]
                          .gen_groups_y[g % NumY]
                          .i_group
                          .gen_router_router_i[t]
                          .gen_router_wide_resp_router_j[p + 1]
                          .i_floo_wide_resp_router.ready_i[router_p + 1]
                      )
                    );
              end
            end
          end
        end
      end
    end
  endgenerate

  always_ff @(posedge clk) begin
    if (rst_n) begin
      // if (cycle_q[19:0] == 'h80000) begin
      if (
          ((cycle_q[63:0] < 'h8000) &&
           ((cycle_q[10:0] == 11'h400) || (cycle_q[10:0] == 11'h000))) ||
          (cycle_q[15:0] == 'h8000)
         ) begin

        $sformat(fn_2, "%s/tile_level_profile_q_%8x.log", log_path, cycle_q);
        f_2 = $fopen(fn_2, "w");
        $display("[Tracer] Logging tile_level_profile_q to %s", fn_2);

        $sformat(fn_3, "%s/group_level_profile_q_%8x.log", log_path, cycle_q);
        f_3 = $fopen(fn_3, "w");
        $display("[Tracer] Logging group_level_profile_q to %s", fn_3);

        $sformat(fn_4, "%s/router_level_profile_q_%8x.log", log_path, cycle_q);
        f_4 = $fopen(fn_4, "w");
        $display("[Tracer] Logging router_level_profile_q to %s", fn_4);

        $sformat(fn_5, "%s/router_local_input_profile_q_%8x.log", log_path, cycle_q);
        f_5 = $fopen(fn_5, "w");
        $display("[Tracer] Logging router_local_input_profile_q to %s", fn_5);

        $timeformat(-9, 0, "", 10);
        $sformat(dump_time, "dump time %t, cycle %8d #;\n", $time, cycle_q);
        $fwrite(f_2, dump_time);
        $fwrite(f_3, dump_time);
        $fwrite(f_4, dump_time);
        $fwrite(f_5, dump_time);

        // tile level
        for (int g = 0; g < NumGroups; g++) begin
          for (int t_i = 0; t_i < NumTilesPerGroup; t_i++) begin
            for (int p = 0; p < (NumRemoteReqPortsPerTile - 1); p++) begin
              automatic string extras_str_2;
              extras_str_2 = $sformatf(
                "{'GROUP': %03d, 'TILE': %03d, 'PORT': %03d, 'req_vld_cyc_num': %03d, 'req_hsk_cyc_num': %03d, 'util': %.2f\n",
                g, t_i, p,
                tile_level_profile_q[g][t_i].req_vld_cyc_num[p],
                tile_level_profile_q[g][t_i].req_hsk_cyc_num[p],
                (tile_level_profile_q[g][t_i].req_vld_cyc_num[p] == 0) ? 0.0 :
                ((tile_level_profile_q[g][t_i].req_hsk_cyc_num[p] * 1.0) /
                 (tile_level_profile_q[g][t_i].req_vld_cyc_num[p] * 1.0))
              );
              $fwrite(f_2, extras_str_2);
            end
          end
        end
        $fclose(f_2);

        // group level
        for (int g = 0; g < NumGroups; g++) begin
          int unsigned req_vld_cyc_num_sum;
          int unsigned req_hsk_cyc_num_sum;
          automatic string extras_str_3;

          req_vld_cyc_num_sum = 0;
          req_hsk_cyc_num_sum = 0;

          for (int p = 0; p < (NumRemoteReqPortsPerTile - 1); p++) begin
            req_vld_cyc_num_sum += group_level_profile_q[g].req_vld_cyc_num[p];
            req_hsk_cyc_num_sum += group_level_profile_q[g].req_hsk_cyc_num[p];
          end

          extras_str_3 = $sformatf(
            "{'GROUP': %03d, 'req_vld_cyc_num': %03d, 'req_hsk_cyc_num': %03d, "
            "'req_vld_cyc_more_than_one_hit_same_bank_num': %03d, 'util': %.2f\n",
            g,
            req_vld_cyc_num_sum,
            req_hsk_cyc_num_sum,
            group_level_profile_q[g].req_vld_cyc_more_than_one_hit_same_bank_num,
            ((req_vld_cyc_num_sum - group_level_profile_q[g].req_vld_cyc_more_than_one_hit_same_bank_num) == 0) ?
              0.0 :
              ((req_hsk_cyc_num_sum * 1.0) /
               ((req_vld_cyc_num_sum - group_level_profile_q[g].req_vld_cyc_more_than_one_hit_same_bank_num) * 1.0))
          );

          $fwrite(f_3, extras_str_3);
        end
        $fclose(f_3);

        // router level
        for (int g = 0; g < NumGroups; g++) begin
          for (int t = 0; t < NumTilesPerGroup; t++) begin
            for (int p = 0; p < (NumRemoteReqPortsPerTile - 1); p++) begin
              if (p < NumNarrowRemoteReqPortsPerTile) begin
                // narrow req
                for (int dir = 0; dir < 4; dir++) begin
                  automatic string extras_str_4;
                  extras_str_4 = $sformatf(
                    "{'GROUP': %03d, 'TILE': %03d, 'PORT': %03d, 'REQ_RSP': 0, "
                    "'TYPE': 0, 'DIR': %03d, 'in_vld_cyc_num': %03d, 'in_hsk_cyc_num': %03d, "
                    "'out_vld_cyc_num': %03d, 'out_hsk_cyc_num': %03d, "
                    "'in_util': %.2f, 'out_util': %.2f\n",
                    g, t, p, dir,
                    router_level_profile_req_q[g][t][p].in_vld_cyc_num[dir],
                    router_level_profile_req_q[g][t][p].in_hsk_cyc_num[dir],
                    router_level_profile_req_q[g][t][p].out_vld_cyc_num[dir],
                    router_level_profile_req_q[g][t][p].out_hsk_cyc_num[dir],
                    (router_level_profile_req_q[g][t][p].in_vld_cyc_num[dir] > 0) ?
                      (router_level_profile_req_q[g][t][p].in_hsk_cyc_num[dir] * 1.0) /
                      (router_level_profile_req_q[g][t][p].in_vld_cyc_num[dir] * 1.0) :
                      0,
                    (router_level_profile_req_q[g][t][p].out_vld_cyc_num[dir] > 0) ?
                      (router_level_profile_req_q[g][t][p].out_hsk_cyc_num[dir] * 1.0) /
                      (router_level_profile_req_q[g][t][p].out_vld_cyc_num[dir] * 1.0) :
                      0
                  );
                  $fwrite(f_4, extras_str_4);
                end
              end else begin
                // wide req
                for (int dir = 0; dir < 4; dir++) begin
                  automatic string extras_str_4;
                  extras_str_4 = $sformatf(
                    "{'GROUP': %03d, 'TILE': %03d, 'PORT': %03d, 'REQ_RSP': 0, "
                    "'TYPE': 1, 'DIR': %03d, 'in_vld_cyc_num': %03d, 'in_hsk_cyc_num': %03d, "
                    "'out_vld_cyc_num': %03d, 'out_hsk_cyc_num': %03d, "
                    "'in_util': %.2f, 'out_util': %.2f\n",
                    g, t, p, dir,
                    router_level_profile_req_q[g][t][p].in_vld_cyc_num[dir],
                    router_level_profile_req_q[g][t][p].in_hsk_cyc_num[dir],
                    router_level_profile_req_q[g][t][p].out_vld_cyc_num[dir],
                    router_level_profile_req_q[g][t][p].out_hsk_cyc_num[dir],
                    (router_level_profile_req_q[g][t][p].in_vld_cyc_num[dir] > 0) ?
                      (router_level_profile_req_q[g][t][p].in_hsk_cyc_num[dir] * 1.0) /
                      (router_level_profile_req_q[g][t][p].in_vld_cyc_num[dir] * 1.0) :
                      0,
                    (router_level_profile_req_q[g][t][p].out_vld_cyc_num[dir] > 0) ?
                      (router_level_profile_req_q[g][t][p].out_hsk_cyc_num[dir] * 1.0) /
                      (router_level_profile_req_q[g][t][p].out_vld_cyc_num[dir] * 1.0) :
                      0
                  );
                  $fwrite(f_4, extras_str_4);
                end
              end
            end

            // resp
            for (int p = 0; p < (NumRemoteRespPortsPerTile - 1); p++) begin
              for (int dir = 0; dir < 4; dir++) begin
                automatic string extras_str_4;

                extras_str_4 = $sformatf(
                  "{'GROUP': %03d, 'TILE': %03d, 'PORT': %03d, 'REQ_RSP': 1, "
                  "'TYPE': 1, 'DIR': %03d, 'in_vld_cyc_num': %03d, 'in_hsk_cyc_num': %03d, "
                  "'out_vld_cyc_num': %03d, 'out_hsk_cyc_num': %03d, "
                  "'in_util': %.2f, 'out_util': %.2f\n",
                  g, t, p, dir,
                  router_level_profile_resp_q[g][t][p].in_vld_cyc_num[dir],
                  router_level_profile_resp_q[g][t][p].in_hsk_cyc_num[dir],
                  router_level_profile_resp_q[g][t][p].out_vld_cyc_num[dir],
                  router_level_profile_resp_q[g][t][p].out_hsk_cyc_num[dir],
                  (router_level_profile_resp_q[g][t][p].in_vld_cyc_num[dir] > 0) ?
                    (router_level_profile_resp_q[g][t][p].in_hsk_cyc_num[dir] * 1.0) /
                    (router_level_profile_resp_q[g][t][p].in_vld_cyc_num[dir] * 1.0) :
                    0,
                  (router_level_profile_resp_q[g][t][p].out_vld_cyc_num[dir] > 0) ?
                    (router_level_profile_resp_q[g][t][p].out_hsk_cyc_num[dir] * 1.0) /
                    (router_level_profile_resp_q[g][t][p].out_vld_cyc_num[dir] * 1.0) :
                    0
                );

                $fwrite(f_4, extras_str_4);
              end
            end
          end
        end
        $fclose(f_4);

        // router local port
        for (int g = 0; g < NumGroups; g++) begin
          for (int t = 0; t < NumTilesPerGroup; t++) begin
            for (int p = 0; p < (NumRemoteReqPortsPerTile - 1); p++) begin
              if (p < NumNarrowRemoteReqPortsPerTile) begin
                // narrow req
                automatic string extras_str_5;
                extras_str_5 = $sformatf(
                  "{'GROUP': %03d, 'TILE': %03d, 'PORT': %03d, 'REQ_RSP': 0, 'TYPE': 0, "
                  "'req_read_in_num': %03d, 'req_write_in_num': %03d\n",
                  g, t, p,
                  router_local_req_port_profile_q[g][t][p].read_req_num,
                  router_local_req_port_profile_q[g][t][p].write_req_num
                );
                $fwrite(f_5, extras_str_5);
              end else begin
                // wide req
                automatic string extras_str_5;
                extras_str_5 = $sformatf(
                  "{'GROUP': %03d, 'TILE': %03d, 'PORT': %03d, 'REQ_RSP': 0, 'TYPE': 1, "
                  "'req_read_in_num': %03d, 'req_write_in_num': %03d\n",
                  g, t, p,
                  router_local_req_port_profile_q[g][t][p].read_req_num,
                  router_local_req_port_profile_q[g][t][p].write_req_num
                );
                $fwrite(f_5, extras_str_5);
              end
            end

            // resp
            for (int p = 0; p < (NumRemoteRespPortsPerTile - 1); p++) begin
              automatic string extras_str_5;
              extras_str_5 = $sformatf(
                "{'GROUP': %03d, 'TILE': %03d, 'PORT': %03d, 'REQ_RSP': 1, "
                "'TYPE': 1, 'resp_in_num': %03d\n",
                g, t, p,
                router_local_resp_port_profile_q[g][t][p].req_num
              );
              $fwrite(f_5, extras_str_5);
            end
          end
        end

        $fclose(f_5);
      end
    end
  end

  final begin
    $sformat(fn_final_2, "%s/tile_level_profile_q.log", log_path);
    f_final_2 = $fopen(fn_final_2, "w");
    $display("[Tracer] Final Logging Banks to %s", fn_final_2);

    $sformat(fn_final_3, "%s/group_level_profile_q.log", log_path);
    f_final_3 = $fopen(fn_final_3, "w");
    $display("[Tracer] Final Logging Banks to %s", fn_final_3);

    $sformat(fn_final_4, "%s/router_level_profile_q.log", log_path);
    f_final_4 = $fopen(fn_final_4, "w");
    $display("[Tracer] Final Logging Banks to %s", fn_final_4);

    $timeformat(-9, 0, "", 10);
    $sformat(dump_time, "dump time %t, cycle %8d #;\n", $time, cycle_q);
    $fwrite(f_final_2, dump_time);
    $fwrite(f_final_3, dump_time);
    $fwrite(f_final_4, dump_time);

    // tile level
    for (int g = 0; g < NumGroups; g++) begin
      for (int t_i = 0; t_i < NumTilesPerGroup; t_i++) begin
        for (int p = 0; p < (NumRemoteReqPortsPerTile - 1); p++) begin
          automatic string extras_str_final_2;

          extras_str_final_2 = $sformatf(
            "{'GROUP': %03d, 'TILE': %03d, 'PORT': %03d, "
            "'req_vld_cyc_num': %03d, 'req_hsk_cyc_num': %03d, 'util': %.2f\n",
            g, t_i, p,
            tile_level_profile_q[g][t_i].req_vld_cyc_num[p],
            tile_level_profile_q[g][t_i].req_hsk_cyc_num[p],
            (tile_level_profile_q[g][t_i].req_vld_cyc_num[p] == 0) ?
              0.0 :
              (tile_level_profile_q[g][t_i].req_hsk_cyc_num[p] * 1.0) /
              (tile_level_profile_q[g][t_i].req_vld_cyc_num[p] * 1.0)
          );

          $fwrite(f_final_2, extras_str_final_2);
        end
      end
    end
    $fclose(f_final_2);

    // group level
    for (int g = 0; g < NumGroups; g++) begin
      int unsigned req_vld_cyc_num_sum;
      int unsigned req_hsk_cyc_num_sum;
      automatic string extras_str_final_3;

      req_vld_cyc_num_sum = 0;
      req_hsk_cyc_num_sum = 0;

      for (int p = 0; p < (NumRemoteReqPortsPerTile - 1); p++) begin
        req_vld_cyc_num_sum += group_level_profile_q[g].req_vld_cyc_num[p];
        req_hsk_cyc_num_sum += group_level_profile_q[g].req_hsk_cyc_num[p];
      end

      extras_str_final_3 = $sformatf(
        "{'GROUP': %03d, 'req_vld_cyc_num': %03d, 'req_hsk_cyc_num': %03d, "
        "'req_vld_cyc_more_than_one_hit_same_bank_num': %03d, 'util': %.2f\n",
        g,
        req_vld_cyc_num_sum,
        req_hsk_cyc_num_sum,
        group_level_profile_q[g].req_vld_cyc_more_than_one_hit_same_bank_num,
        ((req_vld_cyc_num_sum - group_level_profile_q[g].req_vld_cyc_more_than_one_hit_same_bank_num) == 0) ?
          0.0 :
          (req_hsk_cyc_num_sum * 1.0) /
          ((req_vld_cyc_num_sum - group_level_profile_q[g].req_vld_cyc_more_than_one_hit_same_bank_num) * 1.0)
      );

      $fwrite(f_final_3, extras_str_final_3);
    end
    $fclose(f_final_3);

    // router level
    for (int g = 0; g < NumGroups; g++) begin
      for (int t = 0; t < NumTilesPerGroup; t++) begin
        for (int p = 0; p < (NumRemoteReqPortsPerTile - 1); p++) begin
          if (p < NumNarrowRemoteReqPortsPerTile) begin
            // narrow req
            for (int dir = 0; dir < 4; dir++) begin
              automatic string extras_str_final_4;
              extras_str_final_4 = $sformatf(
                "{'GROUP': %03d, 'TILE': %03d, 'PORT': %03d, 'REQ_RSP': 0, 'TYPE': 0, "
                "'DIR': %03d, 'in_vld_cyc_num': %03d, 'in_hsk_cyc_num': %03d, "
                "'out_vld_cyc_num': %03d, 'out_hsk_cyc_num': %03d, "
                "'in_util': %.2f, 'out_util': %.2f\n",
                g, t, p, dir,
                router_level_profile_req_q[g][t][p].in_vld_cyc_num[dir],
                router_level_profile_req_q[g][t][p].in_hsk_cyc_num[dir],
                router_level_profile_req_q[g][t][p].out_vld_cyc_num[dir],
                router_level_profile_req_q[g][t][p].out_hsk_cyc_num[dir],
                (router_level_profile_req_q[g][t][p].in_vld_cyc_num[dir] > 0) ?
                  (router_level_profile_req_q[g][t][p].in_hsk_cyc_num[dir] * 1.0) /
                  (router_level_profile_req_q[g][t][p].in_vld_cyc_num[dir] * 1.0) : 0,
                (router_level_profile_req_q[g][t][p].out_vld_cyc_num[dir] > 0) ?
                  (router_level_profile_req_q[g][t][p].out_hsk_cyc_num[dir] * 1.0) /
                  (router_level_profile_req_q[g][t][p].out_vld_cyc_num[dir] * 1.0) : 0
              );
              $fwrite(f_final_4, extras_str_final_4);
            end
          end else begin
            // wide req
            for (int dir = 0; dir < 4; dir++) begin
              automatic string extras_str_final_4;
              extras_str_final_4 = $sformatf(
                "{'GROUP': %03d, 'TILE': %03d, 'PORT': %03d, 'REQ_RSP': 0, 'TYPE': 1, "
                "'DIR': %03d, 'in_vld_cyc_num': %03d, 'in_hsk_cyc_num': %03d, "
                "'out_vld_cyc_num': %03d, 'out_hsk_cyc_num': %03d, "
                "'in_util': %.2f, 'out_util': %.2f\n",
                g, t, p, dir,
                router_level_profile_req_q[g][t][p].in_vld_cyc_num[dir],
                router_level_profile_req_q[g][t][p].in_hsk_cyc_num[dir],
                router_level_profile_req_q[g][t][p].out_vld_cyc_num[dir],
                router_level_profile_req_q[g][t][p].out_hsk_cyc_num[dir],
                (router_level_profile_req_q[g][t][p].in_vld_cyc_num[dir] > 0) ?
                  (router_level_profile_req_q[g][t][p].in_hsk_cyc_num[dir] * 1.0) /
                  (router_level_profile_req_q[g][t][p].in_vld_cyc_num[dir] * 1.0) : 0,
                (router_level_profile_req_q[g][t][p].out_vld_cyc_num[dir] > 0) ?
                  (router_level_profile_req_q[g][t][p].out_hsk_cyc_num[dir] * 1.0) /
                  (router_level_profile_req_q[g][t][p].out_vld_cyc_num[dir] * 1.0) : 0
              );
              $fwrite(f_final_4, extras_str_final_4);
            end
          end
        end

        // resp
        for (int p = 0; p < NumRemoteRespPortsPerTile; p++) begin
          for (int dir = 0; dir < 4; dir++) begin
            automatic string extras_str_final_4;
            extras_str_final_4 = $sformatf(
              "{'GROUP': %03d, 'TILE': %03d, 'PORT': %03d, 'REQ_RSP': 1, 'TYPE': 1, "
              "'DIR': %03d, 'in_vld_cyc_num': %03d, 'in_hsk_cyc_num': %03d, "
              "'out_vld_cyc_num': %03d, 'out_hsk_cyc_num': %03d, "
              "'in_util': %.2f, 'out_util': %.2f\n",
              g, t, p, dir,
              router_level_profile_resp_q[g][t][p].in_vld_cyc_num[dir],
              router_level_profile_resp_q[g][t][p].in_hsk_cyc_num[dir],
              router_level_profile_resp_q[g][t][p].out_vld_cyc_num[dir],
              router_level_profile_resp_q[g][t][p].out_hsk_cyc_num[dir],
              (router_level_profile_resp_q[g][t][p].in_vld_cyc_num[dir] > 0) ?
                (router_level_profile_resp_q[g][t][p].in_hsk_cyc_num[dir] * 1.0) /
                (router_level_profile_resp_q[g][t][p].in_vld_cyc_num[dir] * 1.0) : 0,
              (router_level_profile_resp_q[g][t][p].out_vld_cyc_num[dir] > 0) ?
                (router_level_profile_resp_q[g][t][p].out_hsk_cyc_num[dir] * 1.0) /
                (router_level_profile_resp_q[g][t][p].out_vld_cyc_num[dir] * 1.0) : 0
            );
            $fwrite(f_final_4, extras_str_final_4);
          end
        end
      end
    end
    $fclose(f_final_4);
  end

  router_input_profile_t req_router_input_profile_q[NumGroups-1:0][NumTilesPerGroup-1:0][(NumRemoteReqPortsPerTile-1)-1:0];
  floo_rdwr_req_t floo_req_input_queue[NumGroups-1:0][NumTilesPerGroup-1:0][(NumRemoteReqPortsPerTile-1)-1:0][4:0][NumVirtualChannel-1:0][$];
  logic [NumGroups-1:0][NumTilesPerGroup-1:0][(NumRemoteReqPortsPerTile-1)-1:0][4:0][NumVirtualChannel-1:0] floo_req_input_fifo_ready_o;
  logic [NumGroups-1:0][NumTilesPerGroup-1:0][(NumRemoteReqPortsPerTile-1)-1:0][4:0][NumVirtualChannel-1:0] floo_req_input_fifo_valid_i;
  logic [NumGroups-1:0][NumTilesPerGroup-1:0][(NumRemoteReqPortsPerTile-1)-1:0][4:0][NumVirtualChannel-1:0] floo_req_input_fifo_ready_i;
  logic [NumGroups-1:0][NumTilesPerGroup-1:0][(NumRemoteReqPortsPerTile-1)-1:0][4:0][NumVirtualChannel-1:0] floo_req_input_fifo_valid_o;
  logic [NumGroups-1:0][NumTilesPerGroup-1:0][(NumRemoteReqPortsPerTile-1)-1:0][4:0][NumVirtualChannel-1:0] floo_req_output_fifo_ready_o;
  logic [NumGroups-1:0][NumTilesPerGroup-1:0][(NumRemoteReqPortsPerTile-1)-1:0][4:0][NumVirtualChannel-1:0] floo_req_output_fifo_valid_i;
  logic [NumGroups-1:0][NumTilesPerGroup-1:0][(NumRemoteReqPortsPerTile-1)-1:0][4:0][NumVirtualChannel-1:0] floo_req_output_fifo_ready_i;
  logic [NumGroups-1:0][NumTilesPerGroup-1:0][(NumRemoteReqPortsPerTile-1)-1:0][4:0][NumVirtualChannel-1:0] floo_req_output_fifo_valid_o;

  generate
    for (genvar g = 0; g < NumGroups; g++) begin : gen_req_router_input_queue_per_group
      for (genvar t = 0; t < NumTilesPerGroup; t++) begin : gen_req_router_input_queue_per_tile
        for (genvar r = 0; r < (NumRemoteReqPortsPerTile - 1); r++) begin : gen_req_router_input_queue_per_remote_port
          for (genvar router_p = 0; router_p < 5; router_p++) begin : gen_req_router_input_queue_per_dir
            if (r < NumNarrowRemoteReqPortsPerTile) begin
              assign floo_req_input_fifo_ready_o[g][t][r][router_p] =
                dut.i_mempool_cluster.gen_groups_x[g / NumY].gen_groups_y[g % NumY]
                  .i_group.gen_router_router_i[t].gen_router_narrow_req_router_j[r]
                  .i_floo_narrow_req_router.ready_o[router_p];

              assign floo_req_input_fifo_valid_i[g][t][r][router_p] =
                dut.i_mempool_cluster.gen_groups_x[g / NumY].gen_groups_y[g % NumY]
                  .i_group.gen_router_router_i[t].gen_router_narrow_req_router_j[r]
                  .i_floo_narrow_req_router.valid_i[router_p];

              assign floo_req_input_fifo_ready_i[g][t][r][router_p] =
                dut.i_mempool_cluster.gen_groups_x[g / NumY].gen_groups_y[g % NumY]
                  .i_group.gen_router_router_i[t].gen_router_narrow_req_router_j[r]
                  .i_floo_narrow_req_router.in_ready[router_p];

              assign floo_req_input_fifo_valid_o[g][t][r][router_p] =
                dut.i_mempool_cluster.gen_groups_x[g / NumY].gen_groups_y[g % NumY]
                  .i_group.gen_router_router_i[t].gen_router_narrow_req_router_j[r]
                  .i_floo_narrow_req_router.in_valid[router_p];

              assign floo_req_output_fifo_ready_o[g][t][r][router_p] =
                dut.i_mempool_cluster.gen_groups_x[g / NumY].gen_groups_y[g % NumY]
                  .i_group.gen_router_router_i[t].gen_router_narrow_req_router_j[r]
                  .i_floo_narrow_req_router.out_ready[router_p];

              assign floo_req_output_fifo_valid_i[g][t][r][router_p] =
                dut.i_mempool_cluster.gen_groups_x[g / NumY].gen_groups_y[g % NumY]
                  .i_group.gen_router_router_i[t].gen_router_narrow_req_router_j[r]
                  .i_floo_narrow_req_router.out_valid[router_p];

              assign floo_req_output_fifo_ready_i[g][t][r][router_p] =
                dut.i_mempool_cluster.gen_groups_x[g / NumY].gen_groups_y[g % NumY]
                  .i_group.gen_router_router_i[t].gen_router_narrow_req_router_j[r]
                  .i_floo_narrow_req_router.out_buffered_ready[router_p];

              assign floo_req_output_fifo_valid_o[g][t][r][router_p] =
                dut.i_mempool_cluster.gen_groups_x[g / NumY].gen_groups_y[g % NumY]
                  .i_group.gen_router_router_i[t].gen_router_narrow_req_router_j[r]
                  .i_floo_narrow_req_router.out_buffered_valid[router_p];

              for (genvar v = 0; v < NumVirtualChannel; v++) begin : gen_req_router_input_queue_per_vc
                always_ff @(posedge clk) begin
                  if (rst_n) begin
                    if (floo_req_input_fifo_valid_i[g][t][r][router_p][v] &
                        floo_req_input_fifo_ready_o[g][t][r][router_p][v]) begin
                      floo_req_input_queue[g][t][r][router_p][v].push_back(
                        floo_rdwr_req_t'{
                          hdr: dut.i_mempool_cluster.gen_groups_x[g / NumY].gen_groups_y[g % NumY]
                                 .i_group.gen_router_router_i[t].gen_router_narrow_req_router_j[r]
                                 .i_floo_narrow_req_router.data_i[router_p].hdr,
                          payload: '0
                        });
                    end

                    if (floo_req_input_fifo_valid_o[g][t][r][router_p][v] &
                        floo_req_input_fifo_ready_i[g][t][r][router_p][v]) begin
                      floo_req_input_queue[g][t][r][router_p][v].delete(0);
                    end
                  end
                end
              end
            end else begin
              assign floo_req_input_fifo_ready_o[g][t][r][router_p] =
                dut.i_mempool_cluster.gen_groups_x[g / NumY].gen_groups_y[g % NumY]
                  .i_group.gen_router_router_i[t].gen_router_wide_req_router_j[r - NumNarrowRemoteReqPortsPerTile]
                  .i_floo_wide_req_router.ready_o[router_p];

              assign floo_req_input_fifo_valid_i[g][t][r][router_p] =
                dut.i_mempool_cluster.gen_groups_x[g / NumY].gen_groups_y[g % NumY]
                  .i_group.gen_router_router_i[t].gen_router_wide_req_router_j[r - NumNarrowRemoteReqPortsPerTile]
                  .i_floo_wide_req_router.valid_i[router_p];

              assign floo_req_input_fifo_ready_i[g][t][r][router_p] =
                dut.i_mempool_cluster.gen_groups_x[g / NumY].gen_groups_y[g % NumY]
                  .i_group.gen_router_router_i[t].gen_router_wide_req_router_j[r - NumNarrowRemoteReqPortsPerTile]
                  .i_floo_wide_req_router.in_ready[router_p];

              assign floo_req_input_fifo_valid_o[g][t][r][router_p] =
                dut.i_mempool_cluster.gen_groups_x[g / NumY].gen_groups_y[g % NumY]
                  .i_group.gen_router_router_i[t].gen_router_wide_req_router_j[r - NumNarrowRemoteReqPortsPerTile]
                  .i_floo_wide_req_router.in_valid[router_p];

              assign floo_req_output_fifo_ready_o[g][t][r][router_p] =
                dut.i_mempool_cluster.gen_groups_x[g / NumY].gen_groups_y[g % NumY]
                  .i_group.gen_router_router_i[t].gen_router_wide_req_router_j[r - NumNarrowRemoteReqPortsPerTile]
                  .i_floo_wide_req_router.out_ready[router_p];

              assign floo_req_output_fifo_valid_i[g][t][r][router_p] =
                dut.i_mempool_cluster.gen_groups_x[g / NumY].gen_groups_y[g % NumY]
                  .i_group.gen_router_router_i[t].gen_router_wide_req_router_j[r - NumNarrowRemoteReqPortsPerTile]
                  .i_floo_wide_req_router.out_valid[router_p];

              assign floo_req_output_fifo_ready_i[g][t][r][router_p] =
                dut.i_mempool_cluster.gen_groups_x[g / NumY].gen_groups_y[g % NumY]
                  .i_group.gen_router_router_i[t].gen_router_wide_req_router_j[r - NumNarrowRemoteReqPortsPerTile]
                  .i_floo_wide_req_router.out_buffered_ready[router_p];

              assign floo_req_output_fifo_valid_o[g][t][r][router_p] =
                dut.i_mempool_cluster.gen_groups_x[g / NumY].gen_groups_y[g % NumY]
                  .i_group.gen_router_router_i[t].gen_router_wide_req_router_j[r - NumNarrowRemoteReqPortsPerTile]
                  .i_floo_wide_req_router.out_buffered_valid[router_p];

              for (genvar v = 0; v < NumVirtualChannel; v++) begin : gen_req_router_input_queue_per_vc
                always_ff @(posedge clk) begin
                  if (rst_n) begin
                    if (floo_req_input_fifo_valid_i[g][t][r][router_p][v] &
                        floo_req_input_fifo_ready_o[g][t][r][router_p][v]) begin
                      floo_req_input_queue[g][t][r][router_p][v].push_back(
                        dut.i_mempool_cluster.gen_groups_x[g / NumY].gen_groups_y[g % NumY]
                          .i_group.gen_router_router_i[t].gen_router_wide_req_router_j[r - NumNarrowRemoteReqPortsPerTile]
                          .i_floo_wide_req_router.data_i[router_p]);
                    end

                    if (floo_req_input_fifo_valid_o[g][t][r][router_p][v] &
                        floo_req_input_fifo_ready_i[g][t][r][router_p][v]) begin
                      floo_req_input_queue[g][t][r][router_p][v].delete(0);
                    end
                  end
                end
              end
            end
          end
        end
      end
    end
  endgenerate

  function route_direction_e xy_routing (group_xy_id_t group_id, floo_rdwr_req_t floo_req);
    automatic group_xy_id_t dest_id = group_xy_id_t'(floo_req.hdr.dst_id);
    if (dest_id == group_id) begin
      xy_routing = Eject;
    end else if (dest_id.x == group_id.x) begin
      if (dest_id.y < group_id.y) begin
        xy_routing = South;
      end else begin
        xy_routing = North;
      end
    end else begin
      if (dest_id.x < group_id.x) begin
        xy_routing = West;
      end else begin
        xy_routing = East;
      end
    end
  endfunction

  function group_xy_id_t get_next_hop (group_xy_id_t group_id, route_direction_e out_dir);
    if (out_dir == Eject) begin
      get_next_hop = group_id;
    end else if (out_dir == South) begin
      get_next_hop = '{x:group_id.x, y:group_id.y-1};
    end else if (out_dir == North) begin
      get_next_hop = '{x:group_id.x, y:group_id.y+1};
    end else if (out_dir == East) begin
      get_next_hop = '{x:group_id.x+1, y:group_id.y};
    end else if (out_dir == West) begin
      get_next_hop = '{x:group_id.x-1, y:group_id.y};
    end
  endfunction

  function int onehot_to_bin (logic [NumVirtualChannel-1:0] onehot);
    for (int i = 0; i < NumVirtualChannel; i++) begin
        if (onehot[i]) begin
            onehot_to_bin = i;
            break;
        end
    end
  endfunction

  generate
    for (genvar g = 0; g < NumGroups; g++) begin : gen_req_router_input_profile_per_group
      for (genvar t = 0; t < NumTilesPerGroup; t++) begin : gen_req_router_input_profile_per_tile
        for (genvar r = 0; r < (NumRemoteReqPortsPerTile - 1); r++) begin : gen_req_router_input_profile_per_remote_port
          for (genvar router_p = 0; router_p < 5; router_p++) begin : gen_req_router_input_profile_per_dir
            always_ff @(posedge clk or negedge rst_n) begin
              if (!rst_n) begin
                req_router_input_profile_q[g][t][r].in_vld_cyc_num[router_p]       = '0;
                req_router_input_profile_q[g][t][r].in_hsk_cyc_num[router_p]       = '0;
                req_router_input_profile_q[g][t][r].hol_stall_cyc_num[router_p]    = '0;
                req_router_input_profile_q[g][t][r].out_congst_cyc_num[router_p]   = {'0, '0, '0, '0, '0};
                req_router_input_profile_q[g][t][r].cur_stall_cyc_num[router_p]    = '0;
                req_router_input_profile_q[g][t][r].max_stall_cyc_num[router_p]    = '0;
              end else begin
                if ((cycle_q % 200) == 0) begin
                  req_router_input_profile_q[g][t][r].in_vld_cyc_num[router_p]     = '0;
                  req_router_input_profile_q[g][t][r].in_hsk_cyc_num[router_p]     = '0;
                  req_router_input_profile_q[g][t][r].hol_stall_cyc_num[router_p]  = '0;
                  req_router_input_profile_q[g][t][r].out_congst_cyc_num[router_p] = {'0, '0, '0, '0, '0};
                  req_router_input_profile_q[g][t][r].max_stall_cyc_num[router_p]  = '0;
                end

                if (|floo_req_input_fifo_valid_i[g][t][r][router_p]) begin
                  req_router_input_profile_q[g][t][r].in_vld_cyc_num[router_p] += 1;

                  if (|(floo_req_input_fifo_ready_o[g][t][r][router_p] &
                         floo_req_input_fifo_valid_i[g][t][r][router_p])) begin
                    req_router_input_profile_q[g][t][r].in_hsk_cyc_num[router_p] += 1;

                    if (req_router_input_profile_q[g][t][r].cur_stall_cyc_num[router_p] > 0) begin
                      if (req_router_input_profile_q[g][t][r].cur_stall_cyc_num[router_p] >
                          req_router_input_profile_q[g][t][r].max_stall_cyc_num[router_p]) begin
                        req_router_input_profile_q[g][t][r].max_stall_cyc_num[router_p] =
                            req_router_input_profile_q[g][t][r].cur_stall_cyc_num[router_p];
                      end
                      req_router_input_profile_q[g][t][r].cur_stall_cyc_num[router_p] = 0;
                    end
                  end else begin
                    automatic int vc_idx = onehot_to_bin(floo_req_input_fifo_valid_i[g][t][r][router_p]);
                    assert(|floo_req_input_fifo_valid_o[g][t][r][router_p]);

                    req_router_input_profile_q[g][t][r].cur_stall_cyc_num[router_p] += 1;

                    `ifdef XY_ROUTING
                      if (~floo_req_input_fifo_ready_i[g][t][r][router_p][vc_idx]) begin
                        automatic route_direction_e in_dir  = route_direction_e'(router_p);
                        automatic route_direction_e out_dir = xy_routing(g, floo_req_input_queue[g][t][r][router_p][vc_idx][0]);
                        automatic group_xy_id_t cur_hop     = g;
                        automatic logic cont                = '1;

                        req_router_input_profile_q[g][t][r].out_congst_cyc_num[router_p][out_dir] += 1;

                        assert(floo_req_output_fifo_valid_i[g][t][r][out_dir][vc_idx]);

                        while ('1) begin
                          for (int i = 1; i < floo_req_input_queue[cur_hop][t][r][in_dir][vc_idx].size(); i++) begin
                            out_dir = xy_routing(cur_hop, floo_req_input_queue[cur_hop][t][r][in_dir][vc_idx][i]);

                            if (~floo_req_output_fifo_valid_i[cur_hop][t][r][out_dir][vc_idx] &
                                 floo_req_output_fifo_ready_o[cur_hop][t][r][out_dir][vc_idx]) begin
                              req_router_input_profile_q[g][t][r].hol_stall_cyc_num[router_p] += 1;
                              cont = '0;
                              break;
                            end
                          end

                          if (~cont) break;

                          out_dir = xy_routing(cur_hop, floo_req_input_queue[cur_hop][t][r][in_dir][vc_idx][0]);
                          assert(floo_req_output_fifo_valid_i[cur_hop][t][r][out_dir][vc_idx]);

                          if (floo_req_output_fifo_ready_o[cur_hop][t][r][out_dir][vc_idx] |
                              floo_req_output_fifo_ready_i[cur_hop][t][r][out_dir][vc_idx]) begin
                            break;
                          end

                          if (out_dir == Eject) break;

                          cur_hop = get_next_hop(cur_hop, out_dir);

                          if (out_dir == North) begin
                            in_dir = South;
                          end else if (out_dir == South) begin
                            in_dir = North;
                          end else if (out_dir == East) begin
                            in_dir = West;
                          end else if (out_dir == West) begin
                            in_dir = East;
                          end

                          if (floo_req_input_fifo_ready_i[cur_hop][t][r][in_dir][vc_idx]) begin
                            break;
                          end
                        end
                      end
                    `endif
                  end
                end
              end
            end
          end
        end
      end
    end
  endgenerate

  always_ff @(negedge clk) begin : log_req_router_input_profile
    if (rst_n) begin
      for (int g = 0; g < NumGroups; g++) begin
        for (int t = 0; t < NumTilesPerGroup; t++) begin
          for (int r = 0; r < (NumRemoteReqPortsPerTile - 1); r++) begin
            for (int router_p = 0; router_p < 5; router_p++) begin
              if ((cycle_q % 200) == 199) begin
                automatic string log_str;

                log_str = $sformatf(
                  "{'GROUP': %03d, 'TILE': %03d, 'PORT': %03d, 'DIR': %03d, "
                  "'start_cycle': %03d, 'end_cycle': %03d, "
                  "'in_vld_cyc_num': %03d, 'in_hsk_cyc_num': %03d, "
                  "'hol_stall_cyc_num': %03d, 'max_stall_cyc_num': %03d, "
                  "'out_dir0_cong_cyc_num': %03d, 'out_dir1_cong_cyc_num': %03d, "
                  "'out_dir2_cong_cyc_num': %03d, 'out_dir3_cong_cyc_num': %03d, "
                  "'out_dir4_cong_cyc_num': %03d}\n",
                  g, t, r, router_p, cycle_q - 199, cycle_q,
                  req_router_input_profile_q[g][t][r].in_vld_cyc_num[router_p],
                  req_router_input_profile_q[g][t][r].in_hsk_cyc_num[router_p],
                  req_router_input_profile_q[g][t][r].hol_stall_cyc_num[router_p],
                  req_router_input_profile_q[g][t][r].max_stall_cyc_num[router_p],
                  req_router_input_profile_q[g][t][r].out_congst_cyc_num[router_p][0],
                  req_router_input_profile_q[g][t][r].out_congst_cyc_num[router_p][1],
                  req_router_input_profile_q[g][t][r].out_congst_cyc_num[router_p][2],
                  req_router_input_profile_q[g][t][r].out_congst_cyc_num[router_p][3],
                  req_router_input_profile_q[g][t][r].out_congst_cyc_num[router_p][4]
                );

                $fwrite(req_floo_input_log_fd, log_str);
              end
            end
          end
        end
      end
    end
  end

  router_input_profile_t resp_router_input_profile_q[NumGroups-1:0][NumTilesPerGroup-1:0][(NumRemoteRespPortsPerTile-1)-1:0];
  floo_resp_t floo_resp_input_queue[NumGroups-1:0][NumTilesPerGroup-1:0][(NumRemoteRespPortsPerTile-1)-1:0][4:0][NumVirtualChannel-1:0][$];
  logic [NumGroups-1:0][NumTilesPerGroup-1:0][(NumRemoteRespPortsPerTile-1)-1:0][4:0][NumVirtualChannel-1:0] floo_resp_input_fifo_ready_o;
  logic [NumGroups-1:0][NumTilesPerGroup-1:0][(NumRemoteRespPortsPerTile-1)-1:0][4:0][NumVirtualChannel-1:0] floo_resp_input_fifo_valid_i;
  logic [NumGroups-1:0][NumTilesPerGroup-1:0][(NumRemoteRespPortsPerTile-1)-1:0][4:0][NumVirtualChannel-1:0] floo_resp_input_fifo_ready_i;
  logic [NumGroups-1:0][NumTilesPerGroup-1:0][(NumRemoteRespPortsPerTile-1)-1:0][4:0][NumVirtualChannel-1:0] floo_resp_input_fifo_valid_o;
  logic [NumGroups-1:0][NumTilesPerGroup-1:0][(NumRemoteRespPortsPerTile-1)-1:0][4:0][NumVirtualChannel-1:0] floo_resp_output_fifo_ready_o;
  logic [NumGroups-1:0][NumTilesPerGroup-1:0][(NumRemoteRespPortsPerTile-1)-1:0][4:0][NumVirtualChannel-1:0] floo_resp_output_fifo_valid_i;
  logic [NumGroups-1:0][NumTilesPerGroup-1:0][(NumRemoteRespPortsPerTile-1)-1:0][4:0][NumVirtualChannel-1:0] floo_resp_output_fifo_ready_i;
  logic [NumGroups-1:0][NumTilesPerGroup-1:0][(NumRemoteRespPortsPerTile-1)-1:0][4:0][NumVirtualChannel-1:0] floo_resp_output_fifo_valid_o;

  generate
    for (genvar g = 0; g < NumGroups; g++) begin : gen_resp_router_input_queue_per_group
      for (genvar t = 0; t < NumTilesPerGroup; t++) begin : gen_resp_router_input_queue_per_tile
        for (genvar r = 0; r < (NumRemoteRespPortsPerTile - 1); r++) begin : gen_resp_router_input_queue_per_remote_port
          for (genvar router_p = 0; router_p < 5; router_p++) begin : gen_resp_router_input_queue_per_dir
            assign floo_resp_input_fifo_ready_o[g][t][r][router_p] =
              dut.i_mempool_cluster.gen_groups_x[g / NumY].gen_groups_y[g % NumY]
                .i_group.gen_router_router_i[t].gen_router_wide_resp_router_j[r + 1]
                .i_floo_wide_resp_router.ready_o[router_p];

            assign floo_resp_input_fifo_valid_i[g][t][r][router_p] =
              dut.i_mempool_cluster.gen_groups_x[g / NumY].gen_groups_y[g % NumY]
                .i_group.gen_router_router_i[t].gen_router_wide_resp_router_j[r + 1]
                .i_floo_wide_resp_router.valid_i[router_p];

            assign floo_resp_input_fifo_ready_i[g][t][r][router_p] =
              dut.i_mempool_cluster.gen_groups_x[g / NumY].gen_groups_y[g % NumY]
                .i_group.gen_router_router_i[t].gen_router_wide_resp_router_j[r + 1]
                .i_floo_wide_resp_router.in_ready[router_p];

            assign floo_resp_input_fifo_valid_o[g][t][r][router_p] =
              dut.i_mempool_cluster.gen_groups_x[g / NumY].gen_groups_y[g % NumY]
                .i_group.gen_router_router_i[t].gen_router_wide_resp_router_j[r + 1]
                .i_floo_wide_resp_router.in_valid[router_p];

            assign floo_resp_output_fifo_ready_o[g][t][r][router_p] =
              dut.i_mempool_cluster.gen_groups_x[g / NumY].gen_groups_y[g % NumY]
                .i_group.gen_router_router_i[t].gen_router_wide_resp_router_j[r + 1]
                .i_floo_wide_resp_router.out_ready[router_p];

            assign floo_resp_output_fifo_valid_i[g][t][r][router_p] =
              dut.i_mempool_cluster.gen_groups_x[g / NumY].gen_groups_y[g % NumY]
                .i_group.gen_router_router_i[t].gen_router_wide_resp_router_j[r + 1]
                .i_floo_wide_resp_router.out_valid[router_p];

            assign floo_resp_output_fifo_ready_i[g][t][r][router_p] =
              dut.i_mempool_cluster.gen_groups_x[g / NumY].gen_groups_y[g % NumY]
                .i_group.gen_router_router_i[t].gen_router_wide_resp_router_j[r + 1]
                .i_floo_wide_resp_router.out_buffered_ready[router_p];

            assign floo_resp_output_fifo_valid_o[g][t][r][router_p] =
              dut.i_mempool_cluster.gen_groups_x[g / NumY].gen_groups_y[g % NumY]
                .i_group.gen_router_router_i[t].gen_router_wide_resp_router_j[r + 1]
                .i_floo_wide_resp_router.out_buffered_valid[router_p];

            for (genvar v = 0; v < NumVirtualChannel; v++) begin : gen_resp_router_input_queue_per_vc
              always_ff @(posedge clk) begin
                if (rst_n) begin
                  if (floo_resp_input_fifo_valid_i[g][t][r][router_p][v] &
                      floo_resp_input_fifo_ready_o[g][t][r][router_p][v]) begin
                    floo_resp_input_queue[g][t][r][router_p][v].push_back(
                      dut.i_mempool_cluster.gen_groups_x[g / NumY].gen_groups_y[g % NumY]
                        .i_group.gen_router_router_i[t].gen_router_wide_resp_router_j[r + 1]
                        .i_floo_wide_resp_router.data_i[router_p]);
                  end

                  if (floo_resp_input_fifo_valid_o[g][t][r][router_p][v] &
                      floo_resp_input_fifo_ready_i[g][t][r][router_p][v]) begin
                    floo_resp_input_queue[g][t][r][router_p][v].delete(0);
                  end
                end
              end
            end
          end
        end
      end
    end
  endgenerate

  function route_direction_e resp_xy_routing (group_xy_id_t group_id, floo_resp_t floo_resp);
    automatic group_xy_id_t dest_id = group_xy_id_t'(floo_resp.hdr.dst_id);
    if (dest_id == group_id) begin
      resp_xy_routing = Eject;
    end else if (dest_id.x == group_id.x) begin
      if (dest_id.y < group_id.y) begin
        resp_xy_routing = South;
      end else begin
        resp_xy_routing = North;
      end
    end else begin
      if (dest_id.x < group_id.x) begin
        resp_xy_routing = West;
      end else begin
        resp_xy_routing = East;
      end
    end
  endfunction

  generate
    for (genvar g = 0; g < NumGroups; g++) begin : gen_resp_router_input_profile_per_group
      for (genvar t = 0; t < NumTilesPerGroup; t++) begin : gen_resp_router_input_profile_per_tile
        for (genvar r = 0; r < (NumRemoteRespPortsPerTile - 1); r++) begin : gen_resp_router_input_profile_per_remote_port
          for (genvar router_p = 0; router_p < 5; router_p++) begin : gen_resp_router_input_profile_per_dir
            always_ff @(posedge clk or negedge rst_n) begin
              if (!rst_n) begin
                resp_router_input_profile_q[g][t][r].in_vld_cyc_num[router_p]      = '0;
                resp_router_input_profile_q[g][t][r].in_hsk_cyc_num[router_p]      = '0;
                resp_router_input_profile_q[g][t][r].hol_stall_cyc_num[router_p]   = '0;
                resp_router_input_profile_q[g][t][r].out_congst_cyc_num[router_p]  = {'0, '0, '0, '0, '0};
                resp_router_input_profile_q[g][t][r].cur_stall_cyc_num[router_p]   = '0;
                resp_router_input_profile_q[g][t][r].max_stall_cyc_num[router_p]   = '0;
              end else begin
                if ((cycle_q % 200) == 0) begin
                  resp_router_input_profile_q[g][t][r].in_vld_cyc_num[router_p]     = '0;
                  resp_router_input_profile_q[g][t][r].in_hsk_cyc_num[router_p]     = '0;
                  resp_router_input_profile_q[g][t][r].hol_stall_cyc_num[router_p]  = '0;
                  resp_router_input_profile_q[g][t][r].out_congst_cyc_num[router_p] = {'0, '0, '0, '0, '0};
                  resp_router_input_profile_q[g][t][r].max_stall_cyc_num[router_p]  = '0;
                end

                if (|floo_resp_input_fifo_valid_i[g][t][r][router_p]) begin
                  resp_router_input_profile_q[g][t][r].in_vld_cyc_num[router_p] += 1;

                  if (|(floo_resp_input_fifo_ready_o[g][t][r][router_p] &
                         floo_resp_input_fifo_valid_i[g][t][r][router_p])) begin
                    resp_router_input_profile_q[g][t][r].in_hsk_cyc_num[router_p] += 1;

                    if (resp_router_input_profile_q[g][t][r].cur_stall_cyc_num[router_p] > 0) begin
                      if (resp_router_input_profile_q[g][t][r].cur_stall_cyc_num[router_p] >
                          resp_router_input_profile_q[g][t][r].max_stall_cyc_num[router_p]) begin
                        resp_router_input_profile_q[g][t][r].max_stall_cyc_num[router_p] =
                            resp_router_input_profile_q[g][t][r].cur_stall_cyc_num[router_p];
                      end
                      resp_router_input_profile_q[g][t][r].cur_stall_cyc_num[router_p] = 0;
                    end
                  end else begin
                    automatic int vc_idx = onehot_to_bin(floo_resp_input_fifo_valid_i[g][t][r][router_p]);
                    assert(|floo_resp_input_fifo_valid_o[g][t][r][router_p]);

                    resp_router_input_profile_q[g][t][r].cur_stall_cyc_num[router_p] += 1;

                    `ifdef XY_ROUTING
                      if (~floo_resp_input_fifo_ready_i[g][t][r][router_p][vc_idx]) begin
                        automatic route_direction_e in_dir  = route_direction_e'(router_p);
                        automatic route_direction_e out_dir = resp_xy_routing(g, floo_resp_input_queue[g][t][r][router_p][vc_idx][0]);
                        automatic group_xy_id_t cur_hop     = g;
                        automatic logic cont                = '1;

                        resp_router_input_profile_q[g][t][r].out_congst_cyc_num[router_p][out_dir] += 1;
                        assert(floo_resp_output_fifo_valid_i[g][t][r][out_dir][vc_idx]);

                        while ('1) begin
                          for (int i = 1; i < floo_resp_input_queue[cur_hop][t][r][in_dir][vc_idx].size(); i++) begin
                            out_dir = resp_xy_routing(cur_hop, floo_resp_input_queue[cur_hop][t][r][in_dir][vc_idx][i]);

                            if (~floo_resp_output_fifo_valid_i[cur_hop][t][r][out_dir][vc_idx] &
                                 floo_resp_output_fifo_ready_o[cur_hop][t][r][out_dir][vc_idx]) begin
                              resp_router_input_profile_q[g][t][r].hol_stall_cyc_num[router_p] += 1;
                              cont = '0;
                              break;
                            end
                          end

                          if (~cont) break;

                          out_dir = resp_xy_routing(cur_hop, floo_resp_input_queue[cur_hop][t][r][in_dir][vc_idx][0]);
                          assert(floo_resp_output_fifo_valid_i[cur_hop][t][r][out_dir][vc_idx]);

                          if (floo_resp_output_fifo_ready_o[cur_hop][t][r][out_dir][vc_idx] |
                              floo_resp_output_fifo_ready_i[cur_hop][t][r][out_dir][vc_idx]) begin
                            break;
                          end

                          if (out_dir == Eject) break;

                          cur_hop = get_next_hop(cur_hop, out_dir);

                          if (out_dir == North) begin
                            in_dir = South;
                          end else if (out_dir == South) begin
                            in_dir = North;
                          end else if (out_dir == East) begin
                            in_dir = West;
                          end else if (out_dir == West) begin
                            in_dir = East;
                          end

                          if (floo_resp_input_fifo_ready_i[cur_hop][t][r][in_dir][vc_idx]) begin
                            break;
                          end
                        end
                      end
                    `endif
                  end
                end
              end
            end
          end
        end
      end
    end
  endgenerate

  always_ff @(negedge clk) begin : log_resp_router_input_profile
    if (rst_n) begin
      for (int g = 0; g < NumGroups; g++) begin
        for (int t = 0; t < NumTilesPerGroup; t++) begin
          for (int r = 0; r < (NumRemoteRespPortsPerTile - 1); r++) begin
            for (int router_p = 0; router_p < 5; router_p++) begin
              if ((cycle_q % 200) == 199) begin
                automatic string log_str;

                log_str = $sformatf(
                  "{'GROUP': %03d, 'TILE': %03d, 'PORT': %03d, 'DIR': %03d, "
                  "'start_cycle': %03d, 'end_cycle': %03d, "
                  "'in_vld_cyc_num': %03d, 'in_hsk_cyc_num': %03d, "
                  "'hol_stall_cyc_num': %03d, 'max_stall_cyc_num': %03d, "
                  "'out_dir0_cong_cyc_num': %03d, 'out_dir1_cong_cyc_num': %03d, "
                  "'out_dir2_cong_cyc_num': %03d, 'out_dir3_cong_cyc_num': %03d, "
                  "'out_dir4_cong_cyc_num': %03d}\n",
                  g, t, r, router_p, cycle_q - 199, cycle_q,
                  resp_router_input_profile_q[g][t][r].in_vld_cyc_num[router_p],
                  resp_router_input_profile_q[g][t][r].in_hsk_cyc_num[router_p],
                  resp_router_input_profile_q[g][t][r].hol_stall_cyc_num[router_p],
                  resp_router_input_profile_q[g][t][r].max_stall_cyc_num[router_p],
                  resp_router_input_profile_q[g][t][r].out_congst_cyc_num[router_p][0],
                  resp_router_input_profile_q[g][t][r].out_congst_cyc_num[router_p][1],
                  resp_router_input_profile_q[g][t][r].out_congst_cyc_num[router_p][2],
                  resp_router_input_profile_q[g][t][r].out_congst_cyc_num[router_p][3],
                  resp_router_input_profile_q[g][t][r].out_congst_cyc_num[router_p][4]
                );

                $fwrite(resp_floo_input_log_fd, log_str);
              end
            end
          end
        end
      end
    end
  end
`endif // NOC_PROFILING

`ifdef SPM_PROFILING
  int    f_0,   f_1,    f_final_0,  f_final_1;
  string fn_0,  fn_1,   fn_final_0, fn_final_1;
  string app,   log_path;

  initial begin
    void'($value$plusargs("APP=%s", app));
    $sformat(log_path, "../scripts/spm_profiling/run_logs/%s", app);
  end

  profile_t dbg_profile_q[NumGroups-1:0][NumTilesPerGroup-1:0][NumBanksPerTile-1:0][2**TCDMAddrMemWidth-1:0];

  generate
    for (genvar g = 0; g < NumGroups; g++) begin
      for (genvar t = 0; t < NumTilesPerGroup; t++) begin
        for (genvar b = 0; b < NumBanksPerTile; b++) begin
          for(genvar i = 0; i < 2**TCDMAddrMemWidth; i++) begin
            always_ff @(posedge clk or posedge rst_n) begin
              if(cycle_q[7:0] == 'h80) begin
                dbg_profile_q[g][t][b][i].initiated            = dut.i_mempool_cluster.gen_groups_x[g/NumY].gen_groups_y[g%NumY].i_group.i_mempool_group.gen_tiles[t].i_tile.profile_d[b][i].initiated;
                dbg_profile_q[g][t][b][i].initial_cycle        = dut.i_mempool_cluster.gen_groups_x[g/NumY].gen_groups_y[g%NumY].i_group.i_mempool_group.gen_tiles[t].i_tile.profile_d[b][i].initial_cycle;
                dbg_profile_q[g][t][b][i].last_read_cycle      = dut.i_mempool_cluster.gen_groups_x[g/NumY].gen_groups_y[g%NumY].i_group.i_mempool_group.gen_tiles[t].i_tile.profile_d[b][i].last_read_cycle;
                dbg_profile_q[g][t][b][i].last_write_cycle     = dut.i_mempool_cluster.gen_groups_x[g/NumY].gen_groups_y[g%NumY].i_group.i_mempool_group.gen_tiles[t].i_tile.profile_d[b][i].last_write_cycle;
                dbg_profile_q[g][t][b][i].last_access_cycle    = dut.i_mempool_cluster.gen_groups_x[g/NumY].gen_groups_y[g%NumY].i_group.i_mempool_group.gen_tiles[t].i_tile.profile_d[b][i].last_access_cycle;
                dbg_profile_q[g][t][b][i].access_read_number   = dut.i_mempool_cluster.gen_groups_x[g/NumY].gen_groups_y[g%NumY].i_group.i_mempool_group.gen_tiles[t].i_tile.profile_d[b][i].access_read_number;
                dbg_profile_q[g][t][b][i].access_write_number  = dut.i_mempool_cluster.gen_groups_x[g/NumY].gen_groups_y[g%NumY].i_group.i_mempool_group.gen_tiles[t].i_tile.profile_d[b][i].access_write_number;
                dbg_profile_q[g][t][b][i].access_number        = dut.i_mempool_cluster.gen_groups_x[g/NumY].gen_groups_y[g%NumY].i_group.i_mempool_group.gen_tiles[t].i_tile.profile_d[b][i].access_number;
                dbg_profile_q[g][t][b][i].read_cycles          = dut.i_mempool_cluster.gen_groups_x[g/NumY].gen_groups_y[g%NumY].i_group.i_mempool_group.gen_tiles[t].i_tile.profile_d[b][i].read_cycles;
                dbg_profile_q[g][t][b][i].write_cycles         = dut.i_mempool_cluster.gen_groups_x[g/NumY].gen_groups_y[g%NumY].i_group.i_mempool_group.gen_tiles[t].i_tile.profile_d[b][i].write_cycles;
              end
            end
          end
        end
      end
    end
  endgenerate

  always_ff @(posedge clk or posedge rst_n) begin
    if (rst_n) begin
      if ((cycle_q[63:0] == 'h100)  ||
          (cycle_q[63:0] == 'h200)  ||
          (cycle_q[63:0] == 'h400)  ||
          (cycle_q[63:0] == 'h800)  ||
          (cycle_q[63:0] == 'h1000) ||
          (cycle_q[15:0] == 'h8000)) begin

        $sformat(fn_0, "%s/trace_banks_cyc_%8x.dasm",        log_path, cycle_q);
        $sformat(fn_1, "%s/trace_banks_cyc_%8x_inited.dasm", log_path, cycle_q);
        f_1 = $fopen(fn_1, "w");
        $display("[Tracer] Logging Banks to %s, %s", fn_0, fn_1);

        for (int g = 0; g < NumGroups; g++) begin
          for (int t = 0; t < NumTilesPerGroup; t++) begin
            for (int b = 0; b < NumBanksPerTile; b++) begin
              for (int i = 0; i < 2 ** TCDMAddrMemWidth; i++) begin
                automatic string trace_entry;
                automatic string extras_str;

                extras_str = $sformatf(
                  "{'GROUP': %03d, 'TILE': %03d, 'BANK': %03d, 'IDX': 0x%x, "
                  "'inited': %03d, 'ini_cyc': %03d, 'last_rd_cyc': %03d, "
                  "'last_wr_cyc': %03d, 'last_acc_cyc': %03d, "
                  "'acc_rd_num': %03d, 'acc_wr_num': %03d, 'acc_num': %03d, ",
                  g, t, b, i,
                  dbg_profile_q[g][t][b][i].initiated,
                  dbg_profile_q[g][t][b][i].initial_cycle,
                  dbg_profile_q[g][t][b][i].last_read_cycle,
                  dbg_profile_q[g][t][b][i].last_write_cycle,
                  dbg_profile_q[g][t][b][i].last_access_cycle,
                  dbg_profile_q[g][t][b][i].access_read_number,
                  dbg_profile_q[g][t][b][i].access_write_number,
                  dbg_profile_q[g][t][b][i].access_number
                );

                // Append read cycles
                extras_str = $sformatf("%s'rd_cyc': ", extras_str);
                foreach (dbg_profile_q[g][t][b][i].read_cycles[cycle_idx]) begin
                  extras_str = $sformatf(
                    "%s%03d ", extras_str,
                    dbg_profile_q[g][t][b][i].read_cycles[cycle_idx]
                  );
                end
                extras_str = $sformatf("%s, ", extras_str);

                // Append write cycles
                extras_str = $sformatf("%s'wr_cyc': ", extras_str);
                foreach (dbg_profile_q[g][t][b][i].write_cycles[cycle_idx]) begin
                  extras_str = $sformatf(
                    "%s%03d ", extras_str,
                    dbg_profile_q[g][t][b][i].write_cycles[cycle_idx]
                  );
                end
                extras_str = $sformatf("%s}", extras_str);

                // Conditionally log only initialized banks
                if (dbg_profile_q[g][t][b][i].initiated) begin
                  $sformat(trace_entry, "%8d #; %s\n", cycle_q, extras_str);
                  $fwrite(f_1, trace_entry);
                end
              end
            end
          end
        end
        $fclose(f_1);
      end
    end
  end

  final begin
    $sformat(fn_final_0, "%s/trace_banks_cyc_%8x_final.dasm",        log_path, cycle_q);
    $sformat(fn_final_1, "%s/trace_banks_cyc_%8x_inited_final.dasm", log_path, cycle_q);
    f_final_0 = $fopen(fn_final_0, "w");
    f_final_1 = $fopen(fn_final_1, "w");

    $display("[Tracer] Final Logging Banks to %s, %s", fn_final_0, fn_final_1);

    for (int g = 0; g < NumGroups; g++) begin
      for (int t = 0; t < NumTilesPerGroup; t++) begin
        for (int b = 0; b < NumBanksPerTile; b++) begin
          for (int i = 0; i < 2 ** TCDMAddrMemWidth; i++) begin
            automatic string trace_entry_final;
            automatic string extras_str_final;

            extras_str_final = $sformatf(
              "{'GROUP': %03d, 'TILE': %03d, 'BANK': %03d, 'IDX': 0x%x, "
              "'inited': %03d, 'ini_cyc': %03d, 'last_rd_cyc': %03d, "
              "'last_wr_cyc': %03d, 'last_acc_cyc': %03d, "
              "'acc_rd_num': %03d, 'acc_wr_num': %03d, 'acc_num': %03d, ",
              g, t, b, i,
              dbg_profile_q[g][t][b][i].initiated,
              dbg_profile_q[g][t][b][i].initial_cycle,
              dbg_profile_q[g][t][b][i].last_read_cycle,
              dbg_profile_q[g][t][b][i].last_write_cycle,
              dbg_profile_q[g][t][b][i].last_access_cycle,
              dbg_profile_q[g][t][b][i].access_read_number,
              dbg_profile_q[g][t][b][i].access_write_number,
              dbg_profile_q[g][t][b][i].access_number
            );

            // Append read cycles
            extras_str_final = $sformatf("%s'rd_cyc': ", extras_str_final);
            foreach (dbg_profile_q[g][t][b][i].read_cycles[cycle_idx]) begin
              extras_str_final = $sformatf(
                "%s%03d ", extras_str_final,
                dbg_profile_q[g][t][b][i].read_cycles[cycle_idx]
              );
            end
            extras_str_final = $sformatf("%s, ", extras_str_final);

            // Append write cycles
            extras_str_final = $sformatf("%s'wr_cyc': ", extras_str_final);
            foreach (dbg_profile_q[g][t][b][i].write_cycles[cycle_idx]) begin
              extras_str_final = $sformatf(
                "%s%03d ", extras_str_final,
                dbg_profile_q[g][t][b][i].write_cycles[cycle_idx]
              );
            end
            extras_str_final = $sformatf("%s}", extras_str_final);

            // Log to inited trace file if applicable
            if (dbg_profile_q[g][t][b][i].initiated) begin
              $sformat(trace_entry_final, "%8d #; %s\n", cycle_q, extras_str_final);
              $fwrite(f_final_1, trace_entry_final);
            end

            // Log to full trace file
            $sformat(trace_entry_final, "%8d #; %s\n", cycle_q, extras_str_final);
            $fwrite(f_final_0, trace_entry_final);
          end
        end
      end
    end

    $fclose(f_final_0);
    $fclose(f_final_1);
  end
`endif // SPM_PROFILING

`endif // TARGET_VERILATOR
`endif // TARGET_SYNTHESIS

`endif // TB_NOC_PROFILING_SVH_
