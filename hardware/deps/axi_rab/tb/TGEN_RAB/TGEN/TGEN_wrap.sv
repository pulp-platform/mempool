// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

`timescale 1ns/1ps
`define SOD 0.1

module TGEN_wrap
#(
    parameter AXI4_ADDRESS_WIDTH = 32,
    parameter AXI4_RDATA_WIDTH   = 32,
    parameter AXI4_WDATA_WIDTH   = 32,
    parameter AXI4_ID_WIDTH      = 16,
    parameter AXI4_USER_WIDTH    = 10,
    parameter AXI_NUMBYTES       = AXI4_WDATA_WIDTH/8,
    parameter SRC_ID             = 0
)
(
    input logic 					clk,
    input logic 					rst_n,

    AXI_BUS.Master  					axi_port_master,

    input  logic					fetch_en_i,
    output logic					eoc_o,
    output logic [31:0]					PASS_o,
    output logic [31:0]					FAIL_o
);

	TGEN
	#(
	      .AXI4_ADDRESS_WIDTH (  AXI4_ADDRESS_WIDTH  ),
	      .AXI4_RDATA_WIDTH   (  AXI4_RDATA_WIDTH    ),
	      .AXI4_WDATA_WIDTH   (  AXI4_WDATA_WIDTH    ),
	      .AXI4_ID_WIDTH      (  AXI4_ID_WIDTH       ),
	      .AXI4_USER_WIDTH    (  AXI4_USER_WIDTH     ),
	      .SRC_ID             (  SRC_ID              )
	)
	i_TGEN
	(
	      .ACLK     ( clk),
	      .ARESETn  ( rst_n),

	      .AWVALID  ( axi_port_master.aw_valid ),
	      .AWADDR   ( axi_port_master.aw_addr  ),
	      .AWPROT   ( axi_port_master.aw_prot  ),
	      .AWREGION ( axi_port_master.aw_region),
	      .AWLEN    ( axi_port_master.aw_len   ),
	      .AWSIZE   ( axi_port_master.aw_size  ),
	      .AWBURST  ( axi_port_master.aw_burst ),
	      .AWLOCK   ( axi_port_master.aw_lock  ),
	      .AWCACHE  ( axi_port_master.aw_cache ),
	      .AWQOS    ( axi_port_master.aw_qos   ),
	      .AWID     ( axi_port_master.aw_id    ),
	      .AWUSER   ( axi_port_master.aw_user  ),
	      .AWREADY  ( axi_port_master.aw_ready ),

	      .ARVALID  ( axi_port_master.ar_valid ),
	      .ARADDR   ( axi_port_master.ar_addr  ),
	      .ARPROT   ( axi_port_master.ar_prot  ),
	      .ARREGION ( axi_port_master.ar_region),
	      .ARLEN    ( axi_port_master.ar_len   ),
	      .ARSIZE   ( axi_port_master.ar_size  ),
	      .ARBURST  ( axi_port_master.ar_burst ),
	      .ARLOCK   ( axi_port_master.ar_lock  ),
	      .ARCACHE  ( axi_port_master.ar_cache ),
	      .ARQOS    ( axi_port_master.ar_qos   ),
	      .ARID     ( axi_port_master.ar_id    ),
	      .ARUSER   ( axi_port_master.ar_user  ),
	      .ARREADY  ( axi_port_master.ar_ready ),

	      .RVALID   ( axi_port_master.r_valid  ),
	      .RDATA    ( axi_port_master.r_data   ),
	      .RRESP    ( axi_port_master.r_resp   ),
	      .RLAST    ( axi_port_master.r_last   ),
	      .RID      ( axi_port_master.r_id     ),
	      .RUSER    ( axi_port_master.r_user   ),
	      .RREADY   ( axi_port_master.r_ready  ),

	      .WVALID   ( axi_port_master.w_valid  ),
	      .WDATA    ( axi_port_master.w_data   ),
	      .WSTRB    ( axi_port_master.w_strb   ),
	      .WLAST    ( axi_port_master.w_last   ),
	      .WUSER    ( axi_port_master.w_user   ),
	      .WREADY   ( axi_port_master.w_ready  ),

	      .BVALID   ( axi_port_master.b_valid  ),
	      .BRESP    ( axi_port_master.b_resp   ),
	      .BID      ( axi_port_master.b_id     ),
	      .BUSER    ( axi_port_master.b_user   ),
	      .BREADY   ( axi_port_master.b_ready  ),
	      .eoc      ( eoc_o                    ),
	      .fetch_en ( fetch_en_i               ),
	      .PASS     ( PASS_o                   ),
	      .FAIL     ( FAIL_o                   )
	);


endmodule
