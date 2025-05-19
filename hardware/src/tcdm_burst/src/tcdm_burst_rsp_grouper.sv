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

module tcdm_burst_rsp_grouper
  import tcdm_burst_pkg::*;
#(
  parameter int unsigned NumIn  = 32, // number of initiator ports
  parameter int unsigned NumOut = 64, // number of destination ports
  parameter int unsigned DataWidth  = 32,
  // Group Response Extension Grouping Factor for TCDM
  parameter int unsigned  RspGF = 1,
  // Dependant parameters. DO NOT CHANGE!
  parameter int unsigned NumInLog2 = (NumIn == 1) ? 1 : $clog2(NumIn),
  // Burst response type can be overwritten for DataWidth > 32b
  // This can happen when the DataWidth includes transaction metadata
  parameter type burst_resp_t = tcdm_burst_pkg::burst_gresp_t
) (
  input  logic clk_i,
  input  logic rst_ni,
  /// Bank side
  input  logic [RspGF-1:0][NumInLog2-1:0] resp_ini_addr_i,
  input  logic [RspGF-1:0][DataWidth-1:0] resp_rdata_i,
  input  logic [RspGF-1:0]                resp_valid_i,
  output logic [RspGF-1:0]                resp_ready_o,
  /// Xbar side
  output logic         [RspGF-1:0][NumInLog2-1:0] resp_ini_addr_o,
  output logic         [RspGF-1:0][DataWidth-1:0] resp_rdata_o,
  output burst_resp_t  [RspGF-1:0]                resp_burst_o,
  output logic         [RspGF-1:0]                resp_valid_o,
  input  logic         [RspGF-1:0]                resp_ready_i
);

  // Include FF module
  `include "common_cells/registers.svh"

  always_comb begin

    // By default silence all valid ports
    resp_burst_o = '0;
    resp_valid_o = '0;

    // Only send first response data on normal port
    resp_ini_addr_o[0] = resp_ini_addr_i[0];
    resp_rdata_o[0] = resp_rdata_i[0];
    resp_ini_addr_o[RspGF-1:1] = '0;
    resp_rdata_o[RspGF-1:1] = '0;

    // Assign Bank ready from the grouped response ready
    for(int i = 0; i < RspGF; i++) begin
      resp_ready_o[i] = resp_ready_i[0];
    end

    // Wait until all responses are valid
    if (&resp_valid_i) begin
      resp_valid_o[0] = 1'b1;
      for (int unsigned i = 0; i < RspGF-1; i ++) begin
        resp_burst_o[i] = resp_rdata_i[i+1];
      end
    end
  end

  /******************
   *   Assertions   *
   ******************/
  // Check number of cuts.
  if ((RspGF != 1) && ((RspGF % 2) != 0))
    $error("[data_grouper] Grouping Factor has to be a power of two");

  if (RspGF <= 1)
    $error("[data_grouper] Grouping Factor needs to be larger than 1");

endmodule : tcdm_burst_rsp_grouper
