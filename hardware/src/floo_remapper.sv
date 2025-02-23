module floo_remapper #(
  /// Number of inputs into the crossbar (`> 0`).
  parameter int unsigned NumInp      = 32'd0,
  /// Number of outputs from the crossbar (`> 0`).
  parameter int unsigned NumOut      = 32'd0,
  /// Data width of the stream. Can be overwritten by defining the type parameter `payload_t`.
  parameter int unsigned DataWidth   = 32'd1,
  /// Payload type of the data ports, only usage of parameter `DataWidth`.
  parameter type         payload_t   = logic [DataWidth-1:0],
  /// Derived parameter, do **not** overwrite!
  ///
  /// Width of the output selection signal.
  parameter int unsigned SelWidth = (NumOut > 32'd1) ? unsigned'($clog2(NumOut)) : 32'd1,
  /// Derived parameter, do **not** overwrite!
  ///
  /// Signal type definition for selecting the output at the inputs.
  parameter type sel_oup_t = logic[SelWidth-1:0]
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

sel_oup_t [NumInp-1:0] sel_d, sel_q;

always_ff @(posedge clk_i or negedge rst_ni) begin : p_sel_regs
  if(!rst_ni) begin
    for(int i = 0; i < (NumInp / 2); i++) begin : gen_sel_even
      sel_q[i] <= ((i * 2) % NumOut);
    end
    for(int i = (NumInp / 2); i < NumInp; i++) begin : gen_sel_odd
      sel_q[i] <= ((i * 2 - NumInp + 1) % NumOut);
    end
  end else begin
    sel_q <= sel_d;
  end
end

assign sel_d = {sel_q[0], sel_q[NumInp-1:1]};

stream_xbar #(
  .NumInp(NumInp),
  .NumOut(NumOut),
  .payload_t(payload_t),
  .LockIn(1'b0)
) i_stream_xbar (
  .clk_i  (clk_i),
  .rst_ni (rst_ni),
  .flush_i(1'b0),
  .rr_i   ('0),
  .data_i (inp_data_i),
  .sel_i  (sel_q),
  .valid_i(inp_valid_i),
  .ready_o(inp_ready_o),
  .data_o (oup_data_o),
  .idx_o  (),
  .valid_o(oup_valid_o),
  .ready_i(oup_ready_i)
);

endmodule
