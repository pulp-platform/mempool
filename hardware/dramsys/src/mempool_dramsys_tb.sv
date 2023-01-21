// Copyright 2021 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

module mempool_dramsys_tb #(
    /// Axi parameters
    parameter int unsigned AxiAddrWidth                 = mempool_pkg::AddrWidth,
    parameter int unsigned AxiIdWidth                   = mempool_pkg::AxiSystemIdWidth ,
    parameter int unsigned AxiDataWidth                 = mempool_pkg::AxiDataWidth,
    parameter int unsigned AxiUserWidth                 = 1,
    localparam type        dram_data_t                  = logic [AxiDataWidth-1:0],
    localparam type        dram_strb_t                  = logic [AxiDataWidth/8-1:0],
    localparam type        dram_addr_t                  = logic [AxiAddrWidth-1:0],
    localparam type        dram_id_t                    = logic [AxiIdWidth-1:0],
    localparam type        dram_user_t                  = logic,
    localparam type        dram_len_t                   = logic [7:0],
    localparam type        dram_size_t                  = logic [3:0],
    localparam type        dram_resp_t                  = logic [1:0]
)(
    input  logic                    clk_i,
    input  logic                    rst_ni, 
    //AW
    output dram_id_t                aw_id ,
    output dram_addr_t              aw_addr,
    output dram_len_t               aw_len,
    output dram_size_t              aw_size,
    output dram_user_t              aw_user,
    output logic                    aw_valid,
    input  logic                    aw_ready,
    //AR
    output dram_id_t                ar_id,
    output dram_addr_t              ar_addr,
    output dram_len_t               ar_len,
    output dram_size_t              ar_size,
    output dram_user_t              ar_user,
    output logic                    ar_valid,
    input  logic                    ar_ready,
    //R
    input  dram_id_t                r_id,
    input  dram_data_t              r_data,
    input  dram_resp_t              r_resp,
    input  logic                    r_last,
    input  dram_user_t              r_user,
    input  logic                    r_valid,
    output logic                    r_ready,
    //W
    output dram_data_t              w_data,
    // output dram_strb_t              w_strb,
    output logic                    w_last,
    output dram_user_t              w_user,
    output logic                    w_valid,
    input  logic                    w_ready,
    //B
    input  dram_id_t                b_id,
    input  dram_resp_t              b_resp,
    input  dram_user_t              b_user,
    input  logic                    b_valid,
    output logic                    b_ready,
    //EOC
    output logic 										eoc_valid
);

	/*****************
	*  Definitions  *
	*****************/
	import mempool_pkg::*;
	import axi_pkg::xbar_cfg_t;
	import axi_pkg::xbar_rule_32_t;

	`ifdef BOOT_ADDR
	localparam BootAddr = `BOOT_ADDR;
	`else
	localparam BootAddr = 0;
	`endif

  /*********
   *  AXI  *
   *********/

  `include "axi/assign.svh"

  localparam NumAXIMasters = 1;
  localparam NumAXISlaves  = 2;
  localparam NumRules  = NumAXISlaves-1;

  typedef enum logic [$clog2(NumAXISlaves)-1:0] {
    UART,
    Host
  } axi_slave_target;

  axi_system_req_t    [NumAXIMasters - 1:0] axi_mst_req;
  axi_system_resp_t   [NumAXIMasters - 1:0] axi_mst_resp;
  axi_tb_req_t        [NumAXISlaves - 1:0]  axi_mem_req;
  axi_tb_resp_t       [NumAXISlaves - 1:0]  axi_mem_resp;

  axi_system_req_t                          to_mempool_req;
  axi_system_resp_t                         to_mempool_resp;

  localparam xbar_cfg_t XBarCfg = '{
    NoSlvPorts        : NumAXIMasters,
    NoMstPorts        : NumAXISlaves,
    MaxMstTrans       : 4,
    MaxSlvTrans       : 4,
    FallThrough       : 1'b0,
    LatencyMode       : axi_pkg::CUT_MST_PORTS,
    AxiIdWidthSlvPorts: AxiSystemIdWidth,
    AxiIdUsedSlvPorts : AxiSystemIdWidth,
    UniqueIds         : 0,
    AxiAddrWidth      : AddrWidth,
    AxiDataWidth      : DataWidth,
    NoAddrRules       : NumRules
  };

  /*********
   *  DUT  *
   *********/

  logic fetch_en;

  axi_system_req_t    dram_req;
  axi_system_resp_t   dram_resp;

  mempool_system_to_dram #(
    .TCDMBaseAddr(32'h0   ),
    .BootAddr    (BootAddr)
  ) dut (
    .clk_i,
    .rst_ni,
    .fetch_en_i     (fetch_en       ),
    .eoc_valid_o    (eoc_valid      ),
    .busy_o         (/*Unused*/     ),
    .dram_req_o     (dram_req       ),
    .dram_resp_i    (dram_resp      ),
    .mst_req_o      (axi_mst_req    ),
    .mst_resp_i     (axi_mst_resp   ),
    .slv_req_i      (to_mempool_req ),
    .slv_resp_o     (to_mempool_resp)
  );



  /**************
   *  SIM CTRL  *
   **************/

  simulation_ctrl #(
    .axi_system_req_t(axi_system_req_t), 
    .axi_system_resp_t(axi_system_resp_t)
    ) i_simulation_ctrl (
    .clk_i,
    .rst_ni,
    .to_mempool_req_o (to_mempool_req ),
    .to_mempool_resp_i(to_mempool_resp),
    .fetch_o          (fetch_en       )
  );


  /**********************
   *  AXI Interconnect  *
   **********************/

  localparam addr_t UARTBaseAddr = 32'hC000_0000;
  localparam addr_t UARTEndAddr = 32'hC000_FFFF;

  xbar_rule_32_t [NumRules-1:0] xbar_routing_rules = '{
    '{idx: UART, start_addr: UARTBaseAddr, end_addr: UARTEndAddr}
  };

  axi_xbar #(
    .Cfg          (XBarCfg          ),
    .slv_aw_chan_t(axi_system_aw_t  ),
    .mst_aw_chan_t(axi_tb_aw_t      ),
    .w_chan_t     (axi_tb_w_t       ),
    .slv_b_chan_t (axi_system_b_t   ),
    .mst_b_chan_t (axi_tb_b_t       ),
    .slv_ar_chan_t(axi_system_ar_t  ),
    .mst_ar_chan_t(axi_tb_ar_t      ),
    .slv_r_chan_t (axi_system_r_t   ),
    .mst_r_chan_t (axi_tb_r_t       ),
    .slv_req_t    (axi_system_req_t ),
    .slv_resp_t   (axi_system_resp_t),
    .mst_req_t    (axi_tb_req_t     ),
    .mst_resp_t   (axi_tb_resp_t    ),
    .rule_t       (xbar_rule_32_t)
  ) i_testbench_xbar (
    .clk_i,
    .rst_ni,
    .test_i               (1'b0                 ),
    .slv_ports_req_i      (axi_mst_req          ),
    .slv_ports_resp_o     (axi_mst_resp         ),
    .mst_ports_req_o      (axi_mem_req          ),
    .mst_ports_resp_i     (axi_mem_resp         ),
    .addr_map_i           (xbar_routing_rules   ),
    .en_default_mst_port_i('1                   ), // default all slave ports to master port Host
    .default_mst_port_i   ({NumAXIMasters{Host}})
  );

  /**********
   *  HOST  *
   **********/
  assign axi_mem_resp[Host] = '0;

  /**********
   *  UART  *
   **********/

  axi_uart #(
    .axi_req_t (axi_tb_req_t ),
    .axi_resp_t(axi_tb_resp_t)
  ) i_axi_uart (
    .clk_i,
    .rst_ni,
    .testmode_i(1'b0              ),
    .axi_req_i (axi_mem_req[UART] ),
    .axi_resp_o(axi_mem_resp[UART])
  );

	/************
	*  To DRAM  *
	************/

  //AW
  assign aw_id = dram_req.aw.id;
  assign aw_addr = dram_req.aw.addr;
  assign aw_len = dram_req.aw.len;
  assign aw_size = dram_req.aw.size;
  assign aw_user = dram_req.aw.user;
  assign aw_valid = dram_req.aw_valid;
  assign dram_resp.aw_ready = aw_ready;
  //AR
  assign ar_id = dram_req.ar.id;
  assign ar_addr = dram_req.ar.addr;
  assign ar_len = dram_req.ar.len;
  assign ar_size = dram_req.ar.size;
  assign ar_user = dram_req.ar.user;
  assign ar_valid = dram_req.ar_valid;
  assign dram_resp.ar_ready = ar_ready;
  //R
  assign dram_resp.r.id = r_id;
  assign dram_resp.r.data = r_data;
  assign dram_resp.r.resp = r_resp;
  assign dram_resp.r.last = r_last;
  assign dram_resp.r.user = r_user;
  assign dram_resp.r_valid = r_valid;
  assign r_ready = dram_req.r_ready;
  //W
  assign w_data = dram_req.w.data;
  // assign w_strb = dram_req.w.strb;
  assign w_last = dram_req.w.last;
  assign w_user = dram_req.w.user;
  assign w_valid = dram_req.w_valid;
  assign dram_resp.w_ready = w_ready;
  //B
  assign dram_resp.b.id = b_id;
  assign dram_resp.b.resp = b_resp;
  assign dram_resp.b.user = b_user;
  assign dram_resp.b_valid = b_valid;
  assign b_ready = dram_req.b_ready;

  initial begin
    $display("ahahahhaha ----------------------------------------- Good, running!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!");
  end

endmodule : mempool_dramsys_tb
