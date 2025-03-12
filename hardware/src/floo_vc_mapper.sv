// Copyright 2025 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Author: Yinrong Li <yinrli@student.ethz.ch>

module floo_vc_mapper #(
  parameter int unsigned NumVirtChannels   = 32'd0
) (
  input  logic              clk_i,
  input  logic              rst_ni,

  input  logic      valid_i, // NOT AXI, requires ready first
  output logic      ready_o, // NOT AXI, requires ready first

  output logic  [NumVirtChannels-1:0] valid_o, // NOT AXI, requires ready first
  input  logic  [NumVirtChannels-1:0] ready_i  // NOT AXI, requires ready first
);

rr_arb_tree #(
  .NumIn      (NumVirtChannels),
  .DataType   (logic),
  .ExtPrio    (1'b0),
  .AxiVldRdy  (1'b0),
  .LockIn     (1'b1)
) i_arbiter (
  .clk_i  (clk_i),
  .rst_ni (rst_ni),
  .flush_i('0),
  .rr_i   ('0),
  .req_i  (ready_i),
  .gnt_o  (valid_o),
  .data_i ('0),
  .gnt_i  (valid_i),
  .req_o  (ready_o),
  .data_o (),
  .idx_o  ()
);

endmodule
