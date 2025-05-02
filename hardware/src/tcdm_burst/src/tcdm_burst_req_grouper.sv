// Copyright 2023 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Author: Marco Bertuletti ETH Zurich

/// Burst Req Grouper:
/// Packs a parallel memory request from NumIn initiators in a burst request.
/// The burst cutter creates multiple burst requests when the burst request crosses
/// the boundary in the target multi-banked memory.

module tcdm_burst_req_grouper
  import tcdm_burst_pkg::burst_t;
#(
  parameter int unsigned NumIn = 32,
  parameter int unsigned NumOut = 32,
  parameter int unsigned AddrWidth  = 32,
  parameter int unsigned DataWidth  = 32,
  parameter int unsigned BeWidth    = DataWidth/8,
  // Number of Address bits per Target
  parameter int unsigned AddrMemWidth      = 12,
  // Determines the width of the byte offset in a memory word. Normally this can be left at the default value,
  // but sometimes it needs to be overridden (e.g., when metadata is supplied to the memory via the wdata signal).
  parameter int unsigned ByteOffWidth      = $clog2(DataWidth-1)-3,
  // Dependant parameters. DO NOT CHANGE!
  parameter int unsigned NumInLog2 = NumIn == 1 ? 1 : $clog2(NumIn)
)(
  input  logic clk_i,
  input  logic rst_ni,
  // Parallel input request port
  input  logic   [NumIn-1:0][NumInLog2-1:0] req_ini_addr_i, // Initiator address
  input  logic   [NumIn-1:0][AddrWidth-1:0] req_tgt_addr_i, // Target address
  input  logic   [NumIn-1:0][DataWidth-1:0] req_wdata_i,
  input  logic   [NumIn-1:0]                req_wen_i,
  input  logic   [NumIn-1:0][BeWidth]       req_be_i,
  input  logic   [NumIn-1:0]                req_valid_i,
  output logic   [NumIn-1:0]                req_ready_o,
  // Burst output request port
  output logic   [NumIn-1:0][NumInLog2-1:0] req_ini_addr_o, // Initiator address
  output logic   [NumIn-1:0][AddrWidth-1:0] req_tgt_addr_o, // Target address
  output logic   [NumIn-1:0][DataWidth-1:0] req_wdata_o,
  output logic   [NumIn-1:0]                req_wen_o,
  output logic   [NumIn-1:0][BeWidth]       req_be_o,
  output burst_t [NumIn-1:0]                req_burst_o,
  output logic   [NumIn-1:0]                req_valid_o,
  input  logic   [NumIn-1:0]                req_ready_i
);

  `include "common_cells/registers.svh"

  logic [NumIn-1:0][DataWidth-1:0] req_cutter_wdata;
  logic [NumInLog2-1:0]            req_cutter_ini_addr;
  logic [AddrWidth-1:0]            req_cutter_tgt_addr;
  logic                            req_cutter_wen;
  logic [BeWidth-1:0]              req_cutter_be;
  burst_t                          req_cutter_burst;
  logic                            cutter_ready;
  logic                            is_consecutive;

  logic [NumInLog2-1:0] req_bursted_ini_addr;
  logic [AddrWidth-1:0] req_bursted_tgt_addr;
  logic [DataWidth-1:0] req_bursted_wdata;
  logic                 req_bursted_wen;
  logic [BeWidth-1:0]   req_bursted_be;
  burst_t               req_bursted_burst;
  logic                 req_bursted_valid;

  always_comb begin

    // Bypass input
    req_ini_addr_o = req_ini_addr_i;
    req_tgt_addr_o = req_tgt_addr_i;
    req_wdata_o = req_wdata_i;
    req_wen_o = req_wen_i;
    req_be_o = req_be_i;
    req_burst_o = '0;
    req_valid_o = req_valid_i;
    req_ready_o = req_ready_i;

    // Assign input requests to cutter inputs
    req_cutter_tgt_addr = req_tgt_addr_i[0];
    req_cutter_wdata = req_wdata_i;
    req_cutter_wen = req_wen_i[0];
    req_cutter_be = req_be_i[0];
    req_cutter_burst.isburst = 1'b0;
    req_cutter_burst.blen = NumIn;

    is_consecutive = 1'b1;
    for (int i = 1; i < NumIn; i++) begin
      if (req_tgt_addr_i[i] != req_tgt_addr_i[i-1] + (1 << ByteOffWidth)) begin
        is_consecutive = 1'b0;
      end
    end

    // Burst the request
    if (&req_valid_i && !req_wen_i[0] && is_consecutive) begin
      // Send a burst request on the first port
      req_cutter_burst.isburst = 1'b1;
      req_tgt_addr_o[0] = req_bursted_tgt_addr;
      req_wdata_o[0] = req_bursted_wdata;
      req_wen_o[0] = req_bursted_wen;
      req_be_o[0] = req_bursted_be;
      req_burst_o[0] = req_bursted_burst;
      req_valid_o[0] = req_bursted_valid;
      req_ready_o[0] = cutter_ready;
      // Silence other ports
      for (int i = 1; i < NumIn; i++) begin
        req_valid_o[i] = 1'b0;
        req_ready_o[i] = cutter_ready;
      end
    end

  end

  tcdm_burst_cutter #(
    .NumIn        (NumIn        ),
    .NumOut       (NumOut       ),
    .AddrWidth    (AddrWidth    ),
    .DataWidth    (DataWidth    ),
    .BeWidth      (BeWidth      ),
    .AddrMemWidth (AddrMemWidth ),
    .ByteOffWidth (ByteOffWidth )
  ) i_tcdm_burst_cutter (
    .clk_i           (clk_i  ),
    .rst_ni          (rst_ni ),
    // Memory Request In
    .req_ini_addr_i (req_cutter_ini_addr ),
    .req_tgt_addr_i (req_cutter_tgt_addr ),
    .req_wen_i      (req_cutter_wen      ),
    .req_wdata_i    (req_cutter_wdata    ),
    .req_be_i       (req_cutter_be       ),
    .req_burst_i    (req_cutter_burst    ),
    .req_valid_i    (&req_valid_i        ),
    .req_ready_o    (cutter_ready        ),
    // Memory Request Out
    .req_ini_addr_o (req_bursted_ini_addr ),
    .req_tgt_addr_o (req_bursted_tgt_addr ),
    .req_wen_o      (req_bursted_wen      ),
    .req_wdata_o    (req_bursted_wdata    ),
    .req_be_o       (req_bursted_be       ),
    .req_burst_o    (req_bursted_burst    ),
    .req_valid_o    (req_bursted_valid    ),
    .req_ready_i    (req_ready_i[0]       )
  );

endmodule : tcdm_burst_req_grouper
