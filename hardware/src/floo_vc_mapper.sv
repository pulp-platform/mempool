module floo_vc_mapper #(
  parameter int unsigned NumVirtChannels   = 32'd0,
  /// Derived parameter, do **not** overwrite!
  /// Width of the output selection signal.
  parameter int unsigned SelWidth = (NumVirtChannels > 32'd1) ? unsigned'($clog2(NumVirtChannels)) : 32'd1,
  /// Derived parameter, do **not** overwrite!
  ///
  /// Signal type definition for selecting the output at the inputs.
  parameter type sel_t = logic[SelWidth-1:0]
) (
  input  logic              clk_i,
  input  logic              rst_ni,

  input  logic      valid_i, // NOT AXI, requires ready first
  output logic      ready_o, // NOT AXI, requires ready first

  output logic  [NumVirtChannels-1:0] valid_o, // NOT AXI, requires ready first
  input  logic  [NumVirtChannels-1:0] ready_i  // NOT AXI, requires ready first
);

sel_t sel_d, sel_q;

always_ff @(posedge clk_i or negedge rst_ni) begin
  if(!rst_ni) begin
    sel_q <= '0;
  end else begin
    sel_q <= sel_d;
  end
end

// always_comb begin
//   sel_d = sel_q;
//   if (valid_i && ready_o) begin
//     sel_d = (sel_q + 1) % NumVirtChannels;
//   end
// end

always_comb begin
  sel_d = sel_q;
  if (valid_i && ready_o) begin
    if (sel_q == 0) begin
      if (ready_i[1] || !ready_i[0]) begin
        sel_d = 1'b1;
      end
    end
    else begin
      if (ready_i[0] || !ready_i[1]) begin
        sel_d = 1'b0;
      end
    end
  end
  else if (!ready_o) begin
    if (sel_q == 0) begin
      if(ready_i[1]) begin
        sel_d = 1'b1;
      end
    end
    else begin
      if(ready_i[0]) begin
        sel_d = 1'b0;
      end
    end
  end
end

stream_demux #(.N_OUP(NumVirtChannels)) i_handshake_demux (
  .inp_valid_i(valid_i),
  .inp_ready_o(ready_o),
  .oup_sel_i  (sel_q),
  .oup_valid_o(valid_o),
  .oup_ready_i(ready_i)
);

endmodule
