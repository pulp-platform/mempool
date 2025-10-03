// Copyright 2025 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Danilo Cammarata <dcammarata@iis.ee.ethz.ch>
//

timeunit 1ps; timeprecision 1ps;

module opope_tb_wrap;
import opope_pkg::*;

  localparam TCP = 2.0ns; // clock period, 1 GHz clock
  localparam TA  = 0.4ns; // application time
  localparam TT  = 1.6ns; // test time

  logic clk, rst_n, fetch_enable;

  opope_tb #(
    .TCP ( TCP ),
    .TA  ( TA  ),
    .TT  ( TT  ) 
  ) i_opope_tb (
    .clk_i          ( clk          ),
    .rst_ni         ( rst_n        ),
    .fetch_enable_i ( fetch_enable )
  );

  // Performs one entire clock cycle.
  task cycle;
    clk <= #(TCP/2) 0;
    clk <= #TCP 1;
    #TCP;
  endtask

  initial begin
    clk <= 1'b0;
    rst_n <= 1'b0;
    fetch_enable <= 1'b0;
    
    for (int i = 0; i < 20; i++) cycle();

    rst_n <= #TA 1'b1;

    for (int i = 0; i < 10; i++) cycle();

    rst_n <= #TA 1'b0;

    for (int i = 0; i < 10; i++) cycle();

    rst_n <= #TA 1'b1;

    #(100*TCP);
    fetch_enable = 1'b1;

    while(1) cycle();

  end

endmodule // opope_tb_wrap
