// Copyright 2023 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Authors: Sergio Mazzola <smazzola@iis.ee.ethz.ch>
// Description:
// Technology-agnostic combinational cell for operand gating

module operand_gating #(
  parameter type data_t = logic
) (
  input  data_t in_i,
  input  logic  en_i,
  output data_t out_o
);


  // Gate in_i ANDing it with en_i; if gated, is always brought back to 0
  //data_t en_wide;
  //assign en_wide = en_i ? data_t'('1) : data_t'('0);
  //assign out_o   = data_t'(in_i & en_wide);

  always_comb begin
    out_o = data_t'('0);
    if (en_i) begin
      out_o = in_i;
    end
  end

endmodule
