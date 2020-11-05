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

module TGEN_AXI_LITE_wrap 
#( 
      parameter AXI_ADDRESS_WIDTH = 32,
      parameter AXI_RDATA_WIDTH   = 32,
      parameter AXI_WDATA_WIDTH   = 32,
      parameter SRC_ID            = 0
)
(
    input  logic                  clk,
    input  logic                  rst_n,

    AXI_LITE_BUS.Master           cfg_port_master
);


TGEN_AXI_LITE 
#( 
      .AXI_ADDRESS_WIDTH ( AXI_ADDRESS_WIDTH ),
      .AXI_RDATA_WIDTH   ( AXI_RDATA_WIDTH   ),
      .AXI_WDATA_WIDTH   ( AXI_WDATA_WIDTH   ),
      .SRC_ID            ( SRC_ID            )
)
i_TGEN_AXI_LITE
(
    .clk       ( clk                         ),
    .rst_n     ( rst_n                       ),

    // ADDRESS WRITE CHANNEL
    .awaddr_o  ( cfg_port_master.awaddr      ),
    .awvalid_o ( cfg_port_master.awvalid     ),
    .awready_i ( cfg_port_master.awready     ),

    // ADDRESS READ CHANNEL
    .araddr_o  ( cfg_port_master.araddr      ),
    .arvalid_o ( cfg_port_master.arvalid     ),
    .arready_i ( cfg_port_master.arready     ),

    // ADDRESS WRITE CHANNEL
    .wdata_o   ( cfg_port_master.wdata       ),
    .wstrb_o   ( cfg_port_master.wstrb       ),
    .wvalid_o  ( cfg_port_master.wvalid      ),
    .wready_i  ( cfg_port_master.wready      ),

    // Backward write response
    .bready_o  ( cfg_port_master.bready      ),
    .bresp_i   ( cfg_port_master.bresp       ),
    .bvalid_i  ( cfg_port_master.bvalid      ),

     // RESPONSE READ CHANNEL
    .rdata_i   ( cfg_port_master.rdata       ),
    .rvalid_i  ( cfg_port_master.rvalid      ),
    .rready_o  ( cfg_port_master.rready      ),
    .rresp_i   ( cfg_port_master.rresp       )
);

endmodule