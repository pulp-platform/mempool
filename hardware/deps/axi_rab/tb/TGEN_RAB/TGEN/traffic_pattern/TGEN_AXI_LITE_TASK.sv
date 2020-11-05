// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

//--------------- TASK HERE ----------------//

///////////////////////////////////
// ███╗   ██╗ ██████╗ ██████╗    //
// ████╗  ██║██╔═══██╗██╔══██╗   //
// ██╔██╗ ██║██║   ██║██████╔╝   //
// ██║╚██╗██║██║   ██║██╔═══╝    //
// ██║ ╚████║╚██████╔╝██║        //
// ╚═╝  ╚═══╝ ╚═════╝ ╚═╝        //
///////////////////////////////////                         

task Nop;
begin
    #(`SOD);
    awaddr_o  = '0;
    awvalid_o = 1'b0;
    araddr_o  = '0;
    arvalid_o = 1'b0;
    wdata_o   = '0;
    wstrb_o   = '0;
    wvalid_o  = 1'b0;
    bready_o  = 1'b1;
    rready_o  = 1'b1;
    @(posedge clk);
end
endtask


////////////////////////////////////////////////// 
//  ███████╗████████╗ ██████╗ ██████╗ ███████╗  //
//  ██╔════╝╚══██╔══╝██╔═══██╗██╔══██╗██╔════╝  //
//  ███████╗   ██║   ██║   ██║██████╔╝█████╗    //
//  ╚════██║   ██║   ██║   ██║██╔══██╗██╔══╝    //
//  ███████║   ██║   ╚██████╔╝██║  ██║███████╗  //
//  ╚══════╝   ╚═╝    ╚═════╝ ╚═╝  ╚═╝╚══════╝  //
//////////////////////////////////////////////////
                                          
task STORE;
    input [AXI_ADDRESS_WIDTH-1:0]	       		address; 
    input [AXI_WDATA_WIDTH-1:0]				wdata;
    input [AXI_NUMBYTES-1:0]		      		be;    
begin
    #(`SOD);
    awaddr_o  = address;
    awvalid_o = 1'b1;

    araddr_o  = '0;
    arvalid_o = 1'b0;

    wdata_o   = wdata;
    wstrb_o   = be;
    wvalid_o  = 1'b1;

    bready_o  = 1'b1;
    rready_o  = 1'b1;

    fork
      WAIT_AW_GRANT();
      WAIT_DW_GRANT();
    join

    @(WriteDone);
end
endtask

/////////////////////////////////////////
//  ██╗      ██████╗  █████╗ ██████╗   //
//  ██║     ██╔═══██╗██╔══██╗██╔══██╗  //
//  ██║     ██║   ██║███████║██║  ██║  //
//  ██║     ██║   ██║██╔══██║██║  ██║  //
//  ███████╗╚██████╔╝██║  ██║██████╔╝  //
//  ╚══════╝ ╚═════╝ ╚═╝  ╚═╝╚═════╝   //
/////////////////////////////////////////            
                     
task LOAD;
    input [AXI_ADDRESS_WIDTH-1:0]	       		address;  
begin
    #(`SOD);
    awaddr_o  = '0;
    awvalid_o = 1'b0;

    araddr_o  = address;
    arvalid_o = 1'b1;

    wdata_o   = '0;
    wstrb_o   = '0;
    wvalid_o  = 1'b0;

    bready_o  = 1'b1;
    rready_o  = 1'b1;
    
    WAIT_AR_GRANT();

    @(ReadDone);
end
endtask




task WAIT_DW_GRANT;
begin
    @(req_DW_granted);
    wdata_o   = '0;
    wstrb_o   = '0;
    wvalid_o  = 1'b0;
end
endtask

task WAIT_AW_GRANT;
begin
    @(req_AW_granted);
    awaddr_o   = '0;
    awvalid_o  = 1'b0;
end
endtask

task WAIT_AR_GRANT;
begin
    @(req_AR_granted);
    araddr_o   = '0;
    arvalid_o  = 1'b0;
end
endtask
  