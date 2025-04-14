// Copyright 2023 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Author: Diyou Shen ETH Zurich
//
//
// Description:
// This module is used to check if the parallel responses can be grouped into
// a single response (by default rsp_o[0])
// This could reduce the number of traffic on the rsp channel for remote loads 

module tcdm_burst_rsp_grouper #(
  /// Response channel data grouping factor
  parameter int unsigned              RspGF             = 1,
  parameter type                      addr_t            = logic,
  parameter type                      rsp_payload_t     = logic
) (
  input  logic                        clk_i,
  input  logic                        rst_ni,
  /// Do we group the response?
  input  logic                        group_i,

  input  rsp_payload_t  [RspGF-1:0]   rsp_payload_i,
  input  addr_t         [RspGF-1:0]   rsp_addr_i,
  input  logic          [RspGF-1:0]   rsp_wide_i,
  input  logic          [RspGF-1:0]   rsp_valid_i,
  output logic          [RspGF-1:0]   rsp_ready_o,

  output rsp_payload_t  [RspGF-1:0]   rsp_payload_o,
  output addr_t         [RspGF-1:0]   rsp_addr_o,
  output logic          [RspGF-1:0]   rsp_wide_o,
  output logic          [RspGF-1:0]   rsp_valid_o,
  input  logic          [RspGF-1:0]   rsp_ready_i
);
  // Include FF module
  `include "common_cells/registers.svh"
  
  typedef struct packed {
    rsp_payload_t   payload;
    addr_t          ini_addr;
    logic           wide;
  } reg_data_t;

  logic group_d, group_q;
  `FF(group_q, group_d, '0)

  always_comb begin
    // default bypassing signals
    rsp_payload_o = rsp_payload_i;
    rsp_addr_o    = rsp_addr_i;
    rsp_wide_o    = rsp_wide_i;
    rsp_valid_o   = rsp_valid_i;
    rsp_ready_o   = rsp_ready_i;
    // default FF passing
    group_d  = group_q;

    for (int unsigned i = 0; i < RspGF; i ++) begin
      if (rsp_payload_i[i].wen)
        rsp_payload_o[i].rdata.data = '0;
    end

    if (group_i) begin
      // we received a mask, put it into FF
      group_d = group_i;
    end

    // It is possible that previous response has not been picked yet
    // We should wait until it is picked
    if ((&rsp_valid_i) & group_q) begin
      if (rsp_ready_i[0]) begin
        // response is picked, clear mask
        group_d = '0;
      end
      // we need to group these responses
      // mark grouped response as valid
      rsp_payload_o[0].gdata.valid = 1'b1;
      for (int unsigned i = 0; i < RspGF-1; i ++) begin
        // Put data into grouped response
        rsp_payload_o[0].gdata.data[i] = rsp_payload_i[i+1].rdata;
        // Mark original data as invalid
        rsp_payload_o[i+1] = '0;
        rsp_valid_o[i+1]   = '0;
        rsp_wide_o[i+1]    = '0;
        rsp_addr_o[i+1]    = '0;

        // Grouped responses will share the same ready
        rsp_ready_o[i+1]   = rsp_ready_i[0];
      end
    end
  end

  /******************
   *   Assertions   *
   ******************/
  // Check number of cuts.
  if ((RspGF % 2) != 0)
    $error("[data_grouper] Grouping Factor has to be a power of two");

  if (RspGF <= 1)
    $error("[data_grouper] Grouping Factor needs to be larger than 1");
endmodule : tcdm_burst_rsp_grouper
