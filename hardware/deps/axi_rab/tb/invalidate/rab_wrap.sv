`include "axi/assign.svh"
`include "pulp_soc_defines.sv"

module rab_wrap
  #(
    parameter TT,
    parameter TA
    )
  (
   input logic clk_i,
   input logic rst_ni,
   AXI_LITE.in config_in,
   AXI_BUS.in master_in,
   AXI_BUS.out slave_out
   );

  initial begin
    assert(slave_out.AXI_ADDR_WIDTH == master_in.AXI_ADDR_WIDTH);
    assert(slave_out.AXI_DATA_WIDTH == master_in.AXI_DATA_WIDTH);
  end

  AXI_BUS_DV
    #(
      .AXI_ADDR_WIDTH(slave_out.AXI_ADDR_WIDTH),
      .AXI_DATA_WIDTH(slave_out.AXI_DATA_WIDTH),
      .AXI_ID_WIDTH(7),
      .AXI_USER_WIDTH(slave_out.AXI_USER_WIDTH)
      ) unused_slave_dv(clk_i);

  AXI_BUS
    #(
      .AXI_ADDR_WIDTH(slave_out.AXI_ADDR_WIDTH),
      .AXI_DATA_WIDTH(slave_out.AXI_DATA_WIDTH),
      .AXI_ID_WIDTH(7),
      .AXI_USER_WIDTH(slave_out.AXI_USER_WIDTH)
      ) unused_slave();

  `AXI_ASSIGN(unused_slave_dv, unused_slave);

  AXI_BUS_DV
    #(
      .AXI_ADDR_WIDTH(slave_out.AXI_ADDR_WIDTH),
      .AXI_DATA_WIDTH(slave_out.AXI_DATA_WIDTH),
      .AXI_ID_WIDTH(slave_out.AXI_ID_WIDTH),
      .AXI_USER_WIDTH(slave_out.AXI_USER_WIDTH)
      ) unused_slave_acp_dv(clk_i);

  AXI_BUS
    #(
      .AXI_ADDR_WIDTH(slave_out.AXI_ADDR_WIDTH),
      .AXI_DATA_WIDTH(slave_out.AXI_DATA_WIDTH),
      .AXI_ID_WIDTH(slave_out.AXI_ID_WIDTH),
      .AXI_USER_WIDTH(slave_out.AXI_USER_WIDTH)
      ) unused_slave_acp();

  `AXI_ASSIGN(unused_slave_acp_dv, unused_slave_acp);

  AXI_BUS_DV
    #(
      .AXI_ADDR_WIDTH(master_in.AXI_ADDR_WIDTH),
      .AXI_DATA_WIDTH(master_in.AXI_DATA_WIDTH),
      .AXI_ID_WIDTH(14),
      .AXI_USER_WIDTH(master_in.AXI_USER_WIDTH)
      ) unused_master_dv(clk_i);

  AXI_BUS
    #(
      .AXI_ADDR_WIDTH(master_in.AXI_ADDR_WIDTH),
      .AXI_DATA_WIDTH(master_in.AXI_DATA_WIDTH),
      .AXI_ID_WIDTH(14),
      .AXI_USER_WIDTH(master_in.AXI_USER_WIDTH)
      ) unused_master();

  `AXI_ASSIGN(unused_master, unused_master_dv);

  axi_test::axi_driver
    #(
      .AW(slave_out.AXI_ADDR_WIDTH),
      .DW(slave_out.AXI_DATA_WIDTH),
      .IW(7),
      .UW(slave_out.AXI_USER_WIDTH),
      .TA(TA),
      .TT(TT)) unused_slave_drv = new(unused_slave_dv);
  axi_test::axi_driver
    #(
      .AW(slave_out.AXI_ADDR_WIDTH),
      .DW(slave_out.AXI_DATA_WIDTH),
      .IW(slave_out.AXI_ID_WIDTH),
      .UW(slave_out.AXI_USER_WIDTH),
      .TA(TA),
      .TT(TT)) unused_slave_acp_drv = new(unused_slave_acp_dv);
  axi_test::axi_driver
    #(
      .AW(master_in.AXI_ADDR_WIDTH),
      .DW(master_in.AXI_DATA_WIDTH),
      .IW(14),
      .UW(master_in.AXI_USER_WIDTH),
      .TA(TA),
      .TT(TT)) unused_master_drv = new(unused_master_dv);

  // NOTE: not used at the moment
  logic intr_mhf_full, intr_prot, intr_multi, intr_miss;

  axi_rab_wrap
    #(
      .N_PORTS                ( `RAB_N_PORTS             ),
      .N_L2_SETS              ( `RAB_L2_N_SETS           ),
      .N_L2_SET_ENTRIES       ( `RAB_L2_N_SET_ENTRIES    ),
      .AXI_DATA_WIDTH         ( master_in.AXI_DATA_WIDTH ),
      .AXI_USER_WIDTH         ( master_in.AXI_USER_WIDTH ),
      .AXI_INT_ADDR_WIDTH     ( master_in.AXI_ADDR_WIDTH ),
      .AXI_EXT_ADDR_WIDTH     ( slave_out.AXI_ADDR_WIDTH ),
      .AXI_ID_EXT_S_WIDTH     ( slave_out.AXI_ID_WIDTH   ),
      .AXI_ID_EXT_S_ACP_WIDTH ( slave_out.AXI_ID_WIDTH   ),
      .AXI_ID_EXT_M_WIDTH     ( 14                       ),
      .AXI_ID_SOC_S_WIDTH     ( 7                        ),
      // .AXI_ID_SOC_M_WIDTH  ( master_in.AXI_ID_WIDTH   ), // FIXME: why does this give an error...
      .AXI_LITE_DATA_WIDTH    ( config_in.AXI_DATA_WIDTH ),
      .AXI_LITE_ADDR_WIDTH    ( config_in.AXI_ADDR_WIDTH )
      )
  i_axi_rab_wrap
    (
     .clk_i           ( clk_i            ),
     .non_gated_clk_i ( clk_i            ),
     .rst_ni          ( rst_ni           ),
     .rab_lite        ( config_in        ),
     .rab_master      ( slave_out        ),
     .rab_acp         ( unused_slave_acp ),
     .rab_slave       ( unused_master    ),
     .rab_to_socbus   ( unused_slave     ),
     .socbus_to_rab   ( master_in        ),
     .intr_mhf_full_o ( intr_mhf_full    ),
     .intr_prot_o     ( intr_prot        ),
     .intr_multi_o    ( intr_multi       ),
     .intr_miss_o     ( intr_miss        )
     );

  initial begin
    unused_slave_drv.reset_slave();
    unused_slave_drv.axi.w_ready  = 1'b1;
    unused_slave_drv.axi.aw_ready = 1'b1;
    unused_slave_drv.axi.w_ready  = 1'b1;
    unused_slave_acp_drv.reset_slave();
    unused_slave_acp_drv.axi.w_ready  = 1'b1;
    unused_slave_acp_drv.axi.aw_ready = 1'b1;
    unused_slave_acp_drv.axi.w_ready  = 1'b1;
    unused_master_drv.reset_master();
    unused_master_drv.axi.b_ready = 1'b1;
    unused_master_drv.axi.r_ready = 1'b1;
  end
endmodule
