`include "axi/assign.svh"

module base_tb
  #(
    parameter AW,
    parameter DW,
    parameter SIW,
    parameter MIW,
    parameter UW,
    parameter CK,
    parameter TA,
    parameter TT
    )
  (
   AXI_BUS_DV.in master_dv_in,
   AXI_BUS_DV.out slave_dv_out,
   AXI_LITE_DV.in config_dv_in,
   input logic done_i,
   output logic start_o,
   output logic clk_o,
   output int clk_cnt_o
   );

  timeunit      1ps;
  timeprecision 1ps;

  logic clk     = 0;
  logic rst     = 1;
  logic start   = 0;
  int   clk_cnt = 0;

  assign clk_o     = clk;
  assign start_o   = start;
  assign clk_cnt_o = clk_cnt;

  AXI_BUS
    #(
      .AXI_ADDR_WIDTH(AW),
      .AXI_DATA_WIDTH(DW),
      .AXI_ID_WIDTH(SIW),
      .AXI_USER_WIDTH(UW)
      ) slave_out();

  `AXI_ASSIGN(slave_dv_out, slave_out);

  AXI_BUS
    #(
      .AXI_ADDR_WIDTH(AW),
      .AXI_DATA_WIDTH(DW),
      .AXI_ID_WIDTH(MIW),
      .AXI_USER_WIDTH(UW)
      ) master_in();

  `AXI_ASSIGN(master_in, master_dv_in);

  AXI_LITE
    #(
      .AXI_ADDR_WIDTH(AW),
      .AXI_DATA_WIDTH(DW)
      ) config_in();

  `AXI_LITE_ASSIGN(config_in, config_dv_in);

  rab_wrap
    #(
      .TA(TA),
      .TT(TT)
      )
  i_dut
    (
     .clk_i      ( clk       ),
     .rst_ni     ( rst       ),
     .config_in  ( config_in ),
     .master_in  ( master_in ),
     .slave_out  ( slave_out )
     );

  initial begin
    #CK;
    rst <= 0;
    #CK;
    // a clock cycle is needed as the rab has some synchronous resets
    clk <= 1;
    #(CK/2);
    clk <= 0;
    #(CK/2);
    rst <= 1;
    #CK;
    start <= 1;
    clk_cnt <= 0;
    while (!done_i) begin
      clk <= 1;
      #(CK/2);
      clk <= 0;
      #(CK/2);
      clk_cnt <= clk_cnt+1;
    end
    $stop;
  end

endmodule
