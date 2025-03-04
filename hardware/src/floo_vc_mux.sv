// Copyright 2025 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Author: Yinrong Li <yinrli@student.ethz.ch>

module floo_vc_mux #(
  parameter int unsigned NumVirtChannels   = 32'd0,
  /// Data width of the stream. Can be overwritten by defining the type parameter `payload_t`.
  parameter int unsigned DataWidth   = 32'd1,
  /// Payload type of the data ports, only usage of parameter `DataWidth`.
  parameter type         payload_t   = logic [DataWidth-1:0]
) (
  input  logic              clk_i,
  input  logic              rst_ni,

  input  payload_t  data_i,
  input  logic  [NumVirtChannels-1:0]     valid_i, // NOT AXI, requires ready first
  output logic  [NumVirtChannels-1:0]     ready_o, // NOT AXI, requires ready first

  output payload_t  data_o,
  output logic      valid_o, // NOT AXI, requires ready first
  input  logic      ready_i  // NOT AXI, requires ready first
);

logic vc_req_valid, vc_req_ready;

assign vc_req_valid = |valid_i;
assign ready_o = '{NumVirtChannels{vc_req_ready}};

spill_register #(.T(payload_t)) i_spill_register (
  .clk_i  (clk_i),
  .rst_ni (rst_ni),
  .valid_i(vc_req_valid),
  .ready_o(vc_req_ready),
  .data_i (data_i),
  .valid_o(valid_o),
  .ready_i(ready_i),
  .data_o (data_o)
);

endmodule
