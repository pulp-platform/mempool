// Copyright 2024 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Author: Yinrong Li <yinrli@student.ethz.ch>

module floo_remapper #(
  /// Number of inputs into the crossbar (`> 0`).
  parameter int unsigned NumInp      = 32'd0,
  /// Number of outputs from the crossbar (`> 0`).
  parameter int unsigned NumOut      = 32'd0,
  /// Data width of the stream. Can be overwritten by defining the type parameter `payload_t`.
  parameter int unsigned DataWidth   = 32'd1,
  /// Payload type of the data ports, only usage of parameter `DataWidth`.
  parameter type         payload_t   = logic [DataWidth-1:0],
  /// Max number of routers in a remapping group.
  parameter int unsigned GroupSize   = 32'd2,
  /// Interleaved group.
  parameter bit          Interleaved = 1'b0
) (
  input  logic              clk_i,
  input  logic              rst_ni,

  input  payload_t [NumInp-1:0] inp_data_i,
  input  logic     [NumInp-1:0] inp_valid_i,
  output logic     [NumInp-1:0] inp_ready_o,

  output payload_t [NumOut-1:0] oup_data_o,
  output logic     [NumOut-1:0] oup_valid_o,
  input  logic     [NumOut-1:0] oup_ready_i
);

// pragma translate_off
`ifndef VERILATOR
  initial begin : p_assert
    assert(NumInp == NumOut)
      else $fatal(1, "Number of inputs and outputs must be equal.");
    assert ((NumInp % GroupSize) == 0)
      else $fatal(1, "Number of inputs must be divisible by GroupSize.");
    assert ((GroupSize & (GroupSize - 1)) == 0)
      else $fatal(1, "Group size must be a power of 2.");
  end
`endif
// pragma translate_on

localparam int NumGroup = NumInp / GroupSize;
localparam int SelWidth   = $clog2(GroupSize);
localparam type sel_oup_t = logic [SelWidth-1:0];

generate
  for (genvar g = 0; g < NumGroup; g++) begin : gen_remapper
    localparam int start_idx  = g * GroupSize;

    sel_oup_t [GroupSize-1:0] sel_q, sel_d;

    always_ff @(posedge clk_i or negedge rst_ni) begin : p_sel_regs
      if(!rst_ni) begin
        for(int i = 0; i < (GroupSize / 2); i++) begin : gen_sel_even
          sel_q[i] <= (i * 2);
        end
        for(int i = (GroupSize / 2); i < GroupSize; i++) begin : gen_sel_odd
          sel_q[i] <= (i * 2 - GroupSize + 1);
        end
      end else begin
        sel_q <= sel_d;
      end
    end

    assign sel_d = {sel_q[0], sel_q[GroupSize-1:1]};

    if (Interleaved == 1'b1) begin : gen_interleaved_remap
      payload_t [GroupSize-1:0] inp_data_intlv;
      logic     [GroupSize-1:0] inp_valid_intlv;
      logic     [GroupSize-1:0] inp_ready_intlv;
      for (genvar i = 0; i < GroupSize; i++) begin : gen_intlv
        assign inp_data_intlv[i]   = inp_data_i[g + i * NumGroup];
        assign inp_valid_intlv[i]  = inp_valid_i[g + i * NumGroup];
        assign inp_ready_o[g + i * NumGroup] = inp_ready_intlv[i];
      end
      stream_xbar #(
        .NumInp(GroupSize),
        .NumOut(GroupSize),
        .payload_t(payload_t),
        .AxiVldRdy(1'b0),
        .LockIn(1'b0)
      ) i_stream_xbar (
        .clk_i  (clk_i),
        .rst_ni (rst_ni),
        .flush_i(1'b0),
        .rr_i   ('0),
        .data_i (inp_data_intlv),
        .sel_i  (sel_q),
        .valid_i(inp_valid_intlv),
        .ready_o(inp_ready_intlv),
        .data_o (oup_data_o[start_idx +: GroupSize]),
        .idx_o  (),
        .valid_o(oup_valid_o[start_idx +: GroupSize]),
        .ready_i(oup_ready_i[start_idx +: GroupSize])
      );
    end else begin: gen_non_interleaved_remap
      stream_xbar #(
        .NumInp(GroupSize),
        .NumOut(GroupSize),
        .payload_t(payload_t),
        .AxiVldRdy(1'b0),
        .LockIn(1'b0)
      ) i_stream_xbar (
        .clk_i  (clk_i),
        .rst_ni (rst_ni),
        .flush_i(1'b0),
        .rr_i   ('0),
        .data_i (inp_data_i[start_idx +: GroupSize]),
        .sel_i  (sel_q),
        .valid_i(inp_valid_i[start_idx +: GroupSize]),
        .ready_o(inp_ready_o[start_idx +: GroupSize]),
        .data_o (oup_data_o[start_idx +: GroupSize]),
        .idx_o  (),
        .valid_o(oup_valid_o[start_idx +: GroupSize]),
        .ready_i(oup_ready_i[start_idx +: GroupSize])
      );
    end

  end
endgenerate

endmodule
