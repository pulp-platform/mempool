// Copyright 2023 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Author: Marco Bertuletti ETH Zurich
//
//
// Description:
// This module packs a parallel memory request in a burst request

module tcdm_burst_req_grouper #(
  parameter int unsigned TCDMAddrWidth      = 32,
  parameter int unsigned DataWidth          = 32,
  parameter int unsigned NumTCDMPorts       = 4,
  parameter int unsigned NumTiles           = 4,
  parameter int unsigned NumBanksPerTile    = 16,
  parameter int unsigned ByteOffset         = 2,
  parameter type tcdm_req_t                 = logic,
  parameter type tcdm_rsp_t                 = logic,
  parameter type tcdm_breq_t                = logic,
  parameter type meta_id_t                  = logic
)(
  input  logic                   clk_i,
  input  logic                   rst_ni,

  // Parallel input request/response port
  input  tcdm_req_t  [NumTCDMPorts-1:0] req_i,
  input  logic       [NumTCDMPorts-1:0] req_valid_i,
  output logic       [NumTCDMPorts-1:0] req_ready_o,
  output tcdm_rsp_t  [NumTCDMPorts-1:0] rsp_o,
  output logic       [NumTCDMPorts-1:0] rsp_valid_o,
  input  logic       [NumTCDMPorts-1:0] rsp_ready_i,

  // Burst output request/response port
  output tcdm_req_t  [NumTCDMPorts-1:0] req_o,
  output logic       [NumTCDMPorts-1:0] req_valid_o,
  input  logic       [NumTCDMPorts-1:0] req_ready_i,
  input  tcdm_rsp_t  [NumTCDMPorts-1:0] rsp_i,
  input  logic       [NumTCDMPorts-1:0] rsp_valid_i,
  output logic       [NumTCDMPorts-1:0] rsp_ready_o
);

  `include "common_cells/registers.svh"

  /* Request path */

  tcdm_req_t req_cutter;
  tcdm_req_t req_burst;

  logic cutter_ready;
  logic req_valid_burst;

  always_comb begin

    // By default assign inputs to outputs
    req_o[0].tgt_addr         = req_burst.tgt_addr;
    req_o[0].wen              = req_burst.wen;
    req_o[0].wdata.amo        = req_burst.wdata.amo;
    req_o[0].wdata.data       = req_burst.wdata.data;
    req_o[0].be               = req_burst.be;
    req_o[0].wdata.meta_id    = req_burst.wdata.meta_id;
    req_o[0].wdata.core_id    = 1; // Always assign bursts to port 1
    req_o[0].burst            = req_burst.burst;
    req_valid_o[0]            = req_valid_burst;
    for (int i = 1; i < NumTCDMPorts; i++) begin
      req_o[i].tgt_addr       = req_i[i].tgt_addr;
      req_o[i].wen            = req_i[i].wen;
      req_o[i].wdata.amo      = req_i[i].wdata.amo;
      req_o[i].wdata.data     = req_i[i].wdata.data;
      req_o[i].be             = req_i[i].be;
      req_o[i].wdata.meta_id  = req_i[i].wdata.meta_id;
      req_o[i].wdata.core_id  = req_i[i].wdata.core_id;
      req_o[i].burst.isburst  = 1'b0;
      req_o[i].burst.blen     = NumTCDMPorts;
      req_valid_o[i]          = req_valid_i[i];
    end

    // Assign input requests to cutter inputs
    req_cutter.tgt_addr = req_i[0].tgt_addr;
    req_cutter.wen = req_i[0].wen;
    req_cutter.wdata.amo = req_i[0].wdata.amo;
    req_cutter.wdata.data = req_i[0].wdata.data;
    req_cutter.be = req_i[0].be;
    req_cutter.wdata.meta_id = req_i[0].wdata.meta_id;
    req_cutter.burst.isburst = 1'b0;
    req_cutter.burst.blen = NumTCDMPorts;

    // The cutter might need more cycles. Block all requests.
    for (int i = 0; i < NumTCDMPorts; i++) begin
      req_ready_o[i] = cutter_ready;
    end

    // Burst the request
    if (&req_valid_i) begin
      // Send a burst request on the first port
      req_cutter.burst.isburst = 1'b1;
      // Silence other ports
      for (int i = 1; i < NumTCDMPorts; i++) begin
        req_valid_o[i] = 1'b0;
      end
    end

  end

  tcdm_burst_cutter #(
    .NrCut        (1                 ),
    .AddrWidth    (TCDMAddrWidth     ),
    .ByteOffset   (ByteOffset        ),
    .NumTiles     (NumTiles          ),
    .CutLen       (NumBanksPerTile   ),
    .BLenWidth    (NumTCDMPorts      ),
    .tcdm_breq_t  (tcdm_breq_t       ),
    .meta_id_t    (meta_id_t         )
  ) i_tcdm_burst_cutter (
    .clk_i           (clk_i  ),
    .rst_ni          (rst_ni ),
    // Memory Request In
    .req_addr_i      (req_cutter.tgt_addr      ),
    .req_write_i     (req_cutter.wen           ),
    .req_amo_i       (req_cutter.wdata.amo     ),
    .req_data_i      (req_cutter.wdata.data    ),
    .req_strb_i      (req_cutter.be            ),
    .req_id_i        (req_cutter.wdata.meta_id ),
    .req_burst_i     (req_cutter.burst         ),
    .req_valid_i     (req_valid_i[0]           ),
    .req_ready_o     (cutter_ready             ),
    // Memory Request Out
    .req_addr_o      (req_burst.tgt_addr       ),
    .req_write_o     (req_burst.wen            ),
    .req_amo_o       (req_burst.wdata.amo      ),
    .req_data_o      (req_burst.wdata.data     ),
    .req_strb_o      (req_burst.be             ),
    .req_id_o        (req_burst.wdata.meta_id  ),
    .req_burst_o     (req_burst.burst          ),
    .req_valid_o     (req_valid_burst          ),
    .req_ready_i     (req_ready_i[0]           )
  );

  /* Response path */
  logic [$clog2(NumTCDMPorts)-1:0] counter_q, counter_d;
  assign counter_d = rsp_valid_i[0] ? (counter_q == (NumTCDMPorts-1) ? '0 : counter_q + 1)
                     :  counter_q;
  `FF(counter_q, counter_d, '0, clk_i, rst_ni);

  always_comb begin: assign_responses

    // The cutter might need more cycles. Block all requests.
    for (int i = 0; i < NumTCDMPorts; i++) begin
      if (i == counter_q) begin
        rsp_valid_o[i] = rsp_valid_i[0];
      end else begin
        rsp_valid_o[i] = '0;
      end
    end
    // Assign burst requet
    rsp_o[counter_q] = rsp_i[0];
    rsp_ready_o[0] = rsp_ready_i[counter_q];

  end

endmodule : tcdm_burst_req_grouper
