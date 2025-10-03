// Copyright 2025 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Danilo Cammarata <dcammarata@iis.ee.ethz.ch>

module opope_accumulator
  import opope_pkg::*;
#(
  parameter int unsigned   DATA_WIDTH   = BITW,
  parameter int unsigned   DEPTH        = REG_PER_CE
)(
  input  logic                      clk_i               ,
  input  logic                      rst_ni              ,
  input  logic                      flush_i             ,
  input  logic                      iteration_change_i  ,
  input  logic [2*DATA_WIDTH-1:0]   input_i             ,
  input  logic                      write_en_i          ,
  input  logic [$clog2(DEPTH)-1:0]  write_index_i       ,
  input  logic [$clog2(DEPTH)-1:0]  read_index_i        ,
  input  logic                      external_loading    ,
  output logic [2*DATA_WIDTH-1:0]   output_o            
);

  logic [DEPTH-1:0][DATA_WIDTH-1:0] internal_reg_d, internal_reg_q;

  always_comb begin 
    internal_reg_d = internal_reg_q;
    if (write_en_i                    ) internal_reg_d[write_index_i  ] = input_i[  DATA_WIDTH-1:0         ];
    if (write_en_i && external_loading) internal_reg_d[write_index_i+1] = input_i[2*DATA_WIDTH-1:DATA_WIDTH];
  end

  assign output_o    = {internal_reg_q[{read_index_i[1],1'b1}],internal_reg_q[{read_index_i[1],1'b0}]};

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) begin
      internal_reg_q  <= 'b0;
    end else begin
      if (flush_i || iteration_change_i) begin
        internal_reg_q <= 'b0;
      end else begin
        internal_reg_q <= internal_reg_d;
      end
    end
  end

endmodule : opope_accumulator