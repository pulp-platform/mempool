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

module TGEN_AXI_LITE
#(
      parameter AXI_ADDRESS_WIDTH = 32,
      parameter AXI_RDATA_WIDTH   = 32,
      parameter AXI_WDATA_WIDTH   = 32,
      parameter AXI_NUMBYTES       = AXI_WDATA_WIDTH/8,
      parameter SRC_ID             = 0
)
(
    input  logic							clk,
    input  logic							rst_n,

    // ADDRESS WRITE CHANNEL
    output logic [AXI_ADDRESS_WIDTH-1:0] 				awaddr_o,
    output logic							awvalid_o,
    input  logic							awready_i,


    // ADDRESS READ CHANNEL
    output logic [AXI_ADDRESS_WIDTH-1:0]				araddr_o,
    output logic 							arvalid_o,
    input  logic							arready_i,


    // ADDRESS WRITE CHANNEL
    output logic [AXI_WDATA_WIDTH-1:0]					wdata_o,
    output logic [AXI_WDATA_WIDTH/8-1:0]				wstrb_o,
    output logic 							wvalid_o,
    input  logic							wready_i,

    // Backward write response
    output logic 							bready_o,
    input  logic [1:0] 							bresp_i,
    input  logic							bvalid_i,

     // RESPONSE READ CHANNEL
    input  logic  [AXI_RDATA_WIDTH-1:0] 				rdata_i,
    input  logic             		    				rvalid_i,
    output logic             		    				rready_o,
    input  logic [1:0] 							rresp_i
);


    //class color ;
    event 					req_AW_granted;
    event 					req_AR_granted;
    event 					req_DW_granted;
    event					WriteDone;
    event					ReadDone;


    integer 					i,j,k;
    integer 					ID;



    `include "TGEN_AXI_LITE_TASK.sv"


    always @(posedge clk)
    begin
      if((awvalid_o == 1'b1) && (awready_i == 1'b1))
      begin
	-> req_AW_granted;
      end
    end


    always @(posedge clk)
    begin
      if((arvalid_o == 1'b1) && (arready_i == 1'b1))
      begin
	-> req_AR_granted;
      end
    end


    always @(posedge clk)
    begin
      if((wvalid_o == 1'b1) && (wready_i == 1'b1))
      begin
	-> req_DW_granted;
      end
    end

    always @(posedge clk)
    begin
      if((bvalid_i == 1'b1) && (bready_o == 1'b1))
      begin
	-> WriteDone;
      end
    end

    always @(posedge clk)
    begin
      if((rvalid_i == 1'b1) && (rready_o == 1'b1))
      begin
	-> ReadDone;
      end
    end


initial
  begin

    Nop();

    @(posedge clk);
    @(posedge clk);
    @(posedge clk);
    @(posedge clk);
    @(posedge clk);
    @(posedge clk);
    @(posedge clk);
    @(posedge clk);
    @(posedge clk);
    @(posedge clk);
    @(posedge clk);
    @(posedge clk);


    repeat(1)
    begin
      // Write your Config program Here!!!!        Eg 4 regions, and we use only one (Region0)

      // FILL The axi_reg_top conf register 4 Region USED
      STORE( .address(32'h0000_0000), .wdata(32'h0000_0000), .be(4'hf) ); //Start Address Region 0, Master 0;
      STORE( .address(32'h0000_0004), .wdata(32'h0003_FFFF), .be(4'hf) ); //End Address   Region 0, Master 0;
      STORE( .address(32'h0000_0008), .wdata(1), .be(4'hF) );             //VALID RULE,   Region 0, MAster 0;
      STORE( .address(32'h0000_0018), .wdata(0), .be(4'hF) );		  //INVALID RULE, Region 1, MAster 0;
      STORE( .address(32'h0000_0028), .wdata(0), .be(4'hF) );             //INVALID RULE, Region 2, MAster 0;
      STORE( .address(32'h0000_0038), .wdata(0), .be(4'hF) );             //INVALID RULE, Region 3, MAster 0;

      STORE( .address(32'h0000_0040), .wdata(32'h0004_0000), .be(4'hf) ); //Start Address Region 0, Master 1;
      STORE( .address(32'h0000_0044), .wdata(32'h0004_FFFF), .be(4'hf) ); //End Address   Region 0, Master 1;
      STORE( .address(32'h0000_0048), .wdata(1), .be(4'hF) );             //VALID RULE,   Region 0, MAster 1;
      STORE( .address(32'h0000_0058), .wdata(0), .be(4'hF) );		  //INVALID RULE, Region 1, MAster 1;
      STORE( .address(32'h0000_0068), .wdata(0), .be(4'hF) );             //INVALID RULE, Region 2, MAster 1;
      STORE( .address(32'h0000_0078), .wdata(0), .be(4'hF) );             //INVALID RULE, Region 3, MAster 1;

      STORE( .address(32'h0000_0080), .wdata(32'h0005_0000), .be(4'hf) ); //Start Address Region 0, Master 2;
      STORE( .address(32'h0000_0084), .wdata(32'h0005_FFFF), .be(4'hf) ); //End Address   Region 0, Master 2;
      STORE( .address(32'h0000_0088), .wdata(1), .be(4'hF) );             //VALID RULE,   Region 0, MAster 2;
      STORE( .address(32'h0000_0098), .wdata(0), .be(4'hF) );		  //INVALID RULE, Region 1, MAster 2;
      STORE( .address(32'h0000_00A8), .wdata(0), .be(4'hF) );             //INVALID RULE, Region 2, MAster 2;
      STORE( .address(32'h0000_00B8), .wdata(0), .be(4'hF) );             //INVALID RULE, Region 3, MAster 2;

      STORE( .address(32'h0000_00C0), .wdata(32'h0006_0000), .be(4'hf) ); //Start Address Region 0, Master 3;
      STORE( .address(32'h0000_00C4), .wdata(32'h0006_FFFF), .be(4'hf) ); //End Address   Region 0, Master 3;
      STORE( .address(32'h0000_00C8), .wdata(1), .be(4'hF) );             //VALID RULE,   Region 0, MAster 3;
      STORE( .address(32'h0000_00D8), .wdata(0), .be(4'hF) );		  //INVALID RULE, Region 1, MAster 3;
      STORE( .address(32'h0000_00E8), .wdata(0), .be(4'hF) );             //INVALID RULE, Region 2, MAster 3;
      STORE( .address(32'h0000_00F8), .wdata(0), .be(4'hF) );             //INVALID RULE, Region 3, MAster 3;

      STORE( .address(32'h0000_0100), .wdata(32'h0007_0000), .be(4'hf) ); //Start Address Region 0, Master 4;
      STORE( .address(32'h0000_0104), .wdata(32'h0007_FFFF), .be(4'hf) ); //End Address   Region 0, Master 4;
      STORE( .address(32'h0000_0108), .wdata(1), .be(4'hF) );             //VALID RULE,   Region 0, MAster 4;
      STORE( .address(32'h0000_0118), .wdata(0), .be(4'hF) );		  //INVALID RULE, Region 1, MAster 4;
      STORE( .address(32'h0000_0128), .wdata(0), .be(4'hF) );             //INVALID RULE, Region 2, MAster 4;
      STORE( .address(32'h0000_0138), .wdata(0), .be(4'hF) );             //INVALID RULE, Region 3, MAster 4;

      STORE( .address(32'h0000_0140), .wdata(32'h0008_0000), .be(4'hf) ); //Start Address Region 0, Master 5;
      STORE( .address(32'h0000_0144), .wdata(32'h0008_FFFF), .be(4'hf) ); //End Address   Region 0, Master 5;
      STORE( .address(32'h0000_0148), .wdata(1), .be(4'hF) );             //VALID RULE,   Region 0, MAster 5;
      STORE( .address(32'h0000_0158), .wdata(0), .be(4'hF) );		  //INVALID RULE, Region 1, MAster 5;
      STORE( .address(32'h0000_0168), .wdata(0), .be(4'hF) );             //INVALID RULE, Region 2, MAster 5;
      STORE( .address(32'h0000_0178), .wdata(0), .be(4'hF) );             //INVALID RULE, Region 3, MAster 5;

      STORE( .address(32'h0000_0180), .wdata(32'h0009_0000), .be(4'hf) ); //Start Address Region 0, Master 6;
      STORE( .address(32'h0000_0184), .wdata(32'h0009_FFFF), .be(4'hf) ); //End Address   Region 0, Master 6;
      STORE( .address(32'h0000_0188), .wdata(1), .be(4'hF) );             //VALID RULE,   Region 0, MAster 6;
      STORE( .address(32'h0000_0198), .wdata(0), .be(4'hF) );		  //INVALID RULE, Region 1, MAster 6;
      STORE( .address(32'h0000_01A8), .wdata(0), .be(4'hF) );             //INVALID RULE, Region 2, MAster 6;
      STORE( .address(32'h0000_01B8), .wdata(0), .be(4'hF) );             //INVALID RULE, Region 3, MAster 6;

      STORE( .address(32'h0000_01C0), .wdata(32'h000A_0000), .be(4'hf) ); //Start Address Region 0, Master 7;
      STORE( .address(32'h0000_01C4), .wdata(32'h000A_FFFF), .be(4'hf) ); //End Address   Region 0, Master 7;
      STORE( .address(32'h0000_01C8), .wdata(1), .be(4'hF) );             //VALID RULE,   Region 0, MAster 7;
      STORE( .address(32'h0000_01D8), .wdata(0), .be(4'hF) );		  //INVALID RULE, Region 1, MAster 7;
      STORE( .address(32'h0000_01E8), .wdata(0), .be(4'hF) );             //INVALID RULE, Region 2, MAster 7;
      STORE( .address(32'h0000_01F8), .wdata(0), .be(4'hF) );             //INVALID RULE, Region 3, MAster 7;

      //Configure the connectivity map for Slave PORT 0 --> write the LSB
      STORE( .address(32'h0000_0200), .wdata(32'b00000000_00000000_00000000_11111111), .be(4'hF) );  // Slave port 0 (eg Core0) is connected to all master ports (eg memories)

      //Configure the connectivity map for Slave PORT 1
      STORE( .address(32'h0000_0204), .wdata(32'b00000000_00000000_00000000_00001111), .be(4'hF) );  // Slave port 1 is connected to  master ports 0,1,2,3

      //Configure the connectivity map for Slave PORT 2
      STORE( .address(32'h0000_0208), .wdata(32'b00000000_00000000_00000000_00001111), .be(4'hF) );  // Slave port 2 is connected to  master ports 4,5,6,7

      //Configure the connectivity map for Slave PORT 3
      STORE( .address(32'h0000_020C), .wdata(32'b00000000_00000000_00000000_00000011), .be(4'hF) );  // Slave port 1 is connected to  master ports 0,1

    end

    Nop();

    @(negedge clk);
    @(negedge clk);
    @(negedge clk);
    @(negedge clk);
    @(negedge clk);
    @(negedge clk);
    @(negedge clk);
    @(negedge clk);
    @(negedge clk);

end



endmodule
