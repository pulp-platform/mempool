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
      task Nop;
              begin
                  #(`SOD);
                  AWID        = '0;
                  AWADDR      = '0;
                  AWLEN       = '0;
                  AWSIZE      = '0;
                  AWBURST     = '0;
                  AWLOCK      = '0;
                  AWCACHE     = '0;
                  AWPROT      = '0;
                  AWREGION    = '0;
                  AWUSER      = '0;
                  AWQOS       = '0;
                  AWVALID     = '0;

                  WDATA      = '0;
                  WSTRB      = '0;
                  WLAST      = '0;
                  WUSER      = '0;
                  WVALID     = '0;

                  ARID        = '0;
                  ARADDR      = '0;
                  ARLEN       = '0;
                  ARSIZE      = '0;
                  ARBURST     = '0;
                  ARLOCK      = '0;
                  ARCACHE     = '0;
                  ARPROT      = '0;
                  ARREGION    = '0;
                  ARUSER      = '0;
                  ARQOS       = '0;
                  ARVALID     = '0;
                  //@(posedge ACLK);
              end
      endtask


//--------------- TASK HERE ----------------//
      task Nop_AW;
              begin
                  #(`SOD);
                  AWID        <= '0;
                  AWADDR      <= '0;
                  AWLEN       <= '0;
                  AWSIZE      <= '0;
                  AWBURST     <= '0;
                  AWLOCK      <= '0;
                  AWCACHE     <= '0;
                  AWPROT      <= '0;
                  AWREGION    <= '0;
                  AWUSER      <= '0;
                  AWQOS       <= '0;
                  AWVALID     <= '0;
                  @(posedge ACLK);
              end
      endtask


      task Nop_DW;
              begin
                  #(`SOD);
                  WDATA      <= '0;
                  WSTRB      <= '0;
                  WLAST      <= '0;
                  WUSER      <= '0;
                  WVALID     <= '0;
                  @(posedge ACLK);
              end
      endtask


      task Nop_AR;
              begin
                  #(`SOD);
                  ARID        <= '0;
                  ARADDR      <= '0;
                  ARLEN       <= '0;
                  ARSIZE      <= '0;
                  ARBURST     <= '0;
                  ARLOCK      <= '0;
                  ARCACHE     <= '0;
                  ARPROT      <= '0;
                  ARREGION    <= '0;
                  ARUSER      <= '0;
                  ARQOS       <= '0;
                  ARVALID     <= '0;
                  @(posedge ACLK);
              end
      endtask





      task ST4_AW;
              input   [AXI4_ID_WIDTH-1:0]      id;
              input   [AXI4_ADDRESS_WIDTH-1:0] address;
              input   [AXI4_USER_WIDTH-1:0]    user;
              begin
                      #(`SOD);
                      AWID        <=  id;
                      AWADDR      <=  address;
                      AWLEN       <=  8'h00;
                      AWSIZE      <=  3'b010;
                      AWBURST     <=  2'b01;
                      AWLOCK      <= '0;
                      AWCACHE     <= '0;
                      AWPROT      <= '0;
                      AWREGION    <= '0;
                      AWUSER      <=  user;
                      AWQOS       <= '0;
                      AWVALID     <=  1'b1;
                      @(req_AW_granted);
                      AWID        <= '0;
                      AWADDR      <= '0;
                      AWLEN       <= '0;
                      AWSIZE      <= '0;
                      AWBURST     <= '0;
                      AWLOCK      <= '0;
                      AWCACHE     <= '0;
                      AWPROT      <= '0;
                      AWREGION    <= '0;
                      AWUSER      <= '0;
                      AWQOS       <= '0;
                      AWVALID     <= '0;
              end
      endtask


      task ST8_AW;
              input   [AXI4_ID_WIDTH-1:0]      id;
              input   [AXI4_ADDRESS_WIDTH-1:0] address;
              input   [AXI4_USER_WIDTH-1:0]    user;
              begin
                      #(`SOD);
                      AWID        <=  id;
                      AWADDR      <=  address;
                      AWLEN       <=  8'h00;
                      AWSIZE      <=  3'b011;
                      AWBURST     <=  2'b01;
                      AWLOCK      <= '0;
                      AWCACHE     <= '0;
                      AWPROT      <= '0;
                      AWREGION    <= '0;
                      AWUSER      <=  user;
                      AWQOS       <= '0;
                      AWVALID     <=  1'b1;
                      @(req_AW_granted);
                      AWID        <= '0;
                      AWADDR      <= '0;
                      AWLEN       <= '0;
                      AWSIZE      <= '0;
                      AWBURST     <= '0;
                      AWLOCK      <= '0;
                      AWCACHE     <= '0;
                      AWPROT      <= '0;
                      AWREGION    <= '0;
                      AWUSER      <= '0;
                      AWQOS       <= '0;
                      AWVALID     <= '0;
              end
      endtask


      task ST16_AW;
              input   [AXI4_ID_WIDTH-1:0]      id;
              input   [AXI4_ADDRESS_WIDTH-1:0] address;
              input   [AXI4_USER_WIDTH-1:0]    user;
              begin
                      #(`SOD);
                      AWID        <=  id;
                      AWADDR      <=  address;
                      AWLEN       <=  8'h01;
                      AWSIZE      <=  3'b011;
                      AWBURST     <=  2'b01;
                      AWLOCK      <= '0;
                      AWCACHE     <= '0;
                      AWPROT      <= '0;
                      AWREGION    <= '0;
                      AWUSER      <=  user;
                      AWQOS       <= '0;
                      AWVALID     <=  1'b1;
                      @(req_AW_granted);
                      AWID        <= '0;
                      AWADDR      <= '0;
                      AWLEN       <= '0;
                      AWSIZE      <= '0;
                      AWBURST     <= '0;
                      AWLOCK      <= '0;
                      AWCACHE     <= '0;
                      AWPROT      <= '0;
                      AWREGION    <= '0;
                      AWUSER      <= '0;
                      AWQOS       <= '0;
                      AWVALID     <= '0;
              end
      endtask

      task ST24_AW;
              input   [AXI4_ID_WIDTH-1:0]      id;
              input   [AXI4_ADDRESS_WIDTH-1:0] address;
              input   [AXI4_USER_WIDTH-1:0]    user;
              begin
                      #(`SOD);
                      AWID        <=  id;
                      AWADDR      <=  address;
                      AWLEN       <=  8'h02;
                      AWSIZE      <=  3'b011;
                      AWBURST     <=  2'b01;
                      AWLOCK      <= '0;
                      AWCACHE     <= '0;
                      AWPROT      <= '0;
                      AWREGION    <= '0;
                      AWUSER      <=  user;
                      AWQOS       <= '0;
                      AWVALID     <=  1'b1;
                      @(req_AW_granted);
                      AWID        <= '0;
                      AWADDR      <= '0;
                      AWLEN       <= '0;
                      AWSIZE      <= '0;
                      AWBURST     <= '0;
                      AWLOCK      <= '0;
                      AWCACHE     <= '0;
                      AWPROT      <= '0;
                      AWREGION    <= '0;
                      AWUSER      <= '0;
                      AWQOS       <= '0;
                      AWVALID     <= '0;
              end
      endtask


      task ST32_AW;
              input   [AXI4_ID_WIDTH-1:0]      id;
              input   [AXI4_ADDRESS_WIDTH-1:0] address;
              input   [ AXI4_USER_WIDTH-1:0]   user;
              begin
                      #(`SOD);
                      AWID        <=  id;
                      AWADDR      <=  address;
                      AWLEN       <=  8'h03;
                      AWSIZE      <=  3'b011;
                      AWBURST     <=  2'b01;
                      AWLOCK      <= '0;
                      AWCACHE     <= '0;
                      AWPROT      <= '0;
                      AWREGION    <= '0;
                      AWUSER      <=  user;
                      AWQOS       <= '0;
                      AWVALID     <=  1'b1;
                      @(req_AW_granted);
                      AWID        <= '0;
                      AWADDR      <= '0;
                      AWLEN       <= '0;
                      AWSIZE      <= '0;
                      AWBURST     <= '0;
                      AWLOCK      <= '0;
                      AWCACHE     <= '0;
                      AWPROT      <= '0;
                      AWREGION    <= '0;
                      AWUSER      <= '0;
                      AWQOS       <= '0;
                      AWVALID     <= '0;
              end
      endtask

      task ST64_AW;
              input   [AXI4_ID_WIDTH-1:0]      id;
              input   [AXI4_ADDRESS_WIDTH-1:0] address;
              input   [ AXI4_USER_WIDTH-1:0]   user;
              begin
                      #(`SOD);
                      AWID        <=  id;
                      AWADDR      <=  address;
                      AWLEN       <=  8'h07;
                      AWSIZE      <=  3'b011;
                      AWBURST     <=  2'b01;
                      AWLOCK      <= '0;
                      AWCACHE     <= '0;
                      AWPROT      <= '0;
                      AWREGION    <= '0;
                      AWUSER      <=  user;
                      AWQOS       <= '0;
                      AWVALID     <=  1'b1;
                      @(req_AW_granted);
                      AWID        <= '0;
                      AWADDR      <= '0;
                      AWLEN       <= '0;
                      AWSIZE      <= '0;
                      AWBURST     <= '0;
                      AWLOCK      <= '0;
                      AWCACHE     <= '0;
                      AWPROT      <= '0;
                      AWREGION    <= '0;
                      AWUSER      <= '0;
                      AWQOS       <= '0;
                      AWVALID     <= '0;
              end
      endtask

      task ST256_AW;
              input   [AXI4_ID_WIDTH-1:0]      id;
              input   [AXI4_ADDRESS_WIDTH-1:0] address;
              input   [ AXI4_USER_WIDTH-1:0]   user;
              begin
                      #(`SOD);
                      AWID        <=  id;
                      AWADDR      <=  address;
                      AWLEN       <=  8'h1F;
                      AWSIZE      <=  3'b011;
                      AWBURST     <=  2'b01;
                      AWLOCK      <= '0;
                      AWCACHE     <= '0;
                      AWPROT      <= '0;
                      AWREGION    <= '0;
                      AWUSER      <=  user;
                      AWQOS       <= '0;
                      AWVALID     <=  1'b1;
                      @(req_AW_granted);
                      AWID        <= '0;
                      AWADDR      <= '0;
                      AWLEN       <= '0;
                      AWSIZE      <= '0;
                      AWBURST     <= '0;
                      AWLOCK      <= '0;
                      AWCACHE     <= '0;
                      AWPROT      <= '0;
                      AWREGION    <= '0;
                      AWUSER      <= '0;
                      AWQOS       <= '0;
                      AWVALID     <= '0;
              end
      endtask

      task ST4_DW;

              //AXI write data bus -------------- // USED// --------------
              input [AXI4_WDATA_WIDTH-1:0] wdata;
              input [AXI_NUMBYTES-1:0]     be;
              input [AXI4_USER_WIDTH-1:0]  user;
              // ---------------------------------------------------------------


              begin
                      #(`SOD);
                      WDATA  <= wdata;
                      WSTRB  <= be;
                      WLAST  <= 1'b1;
                      WUSER  <= user;
                      WVALID <= 1'b1;
                      @(req_DW_granted);
                      WDATA      <= '0;
                      WSTRB      <= '0;
                      WLAST      <= '0;
                      WUSER      <= '0;
                      WVALID     <= '0;
              end
      endtask



      task ST8_DW;

              //AXI write data bus -------------- // USED// --------------
              input [AXI4_WDATA_WIDTH-1:0] wdata;
              input [AXI_NUMBYTES-1:0]     be;
              input [AXI4_USER_WIDTH-1:0]  user;
              // ---------------------------------------------------------------


              begin
                      #(`SOD);
                      WDATA  <= wdata;
                      WSTRB  <= be;
                      WLAST  <= 1'b1;
                      WUSER  <= user;
                      WVALID <= 1'b1;
                      @(req_DW_granted);
                      WDATA      <= '0;
                      WSTRB      <= '0;
                      WLAST      <= '0;
                      WUSER      <= '0;
                      WVALID     <= '0;
              end
      endtask

      task ST16_DW;

              //AXI write data bus -------------- // USED// --------------
              input  [1:0][AXI4_WDATA_WIDTH-1:0] wdata;
              input  [1:0][AXI_NUMBYTES-1:0]     be;
              input  [AXI4_USER_WIDTH-1:0]       user;
              // ---------------------------------------------------------------


              begin
                      #(`SOD);
                      WDATA  <= wdata[0];
                      WSTRB  <= be[0];
                      WLAST  <= 1'b0;
                      WUSER  <= user;
                      WVALID <= 1'b1;
                      @(req_DW_granted);

                      WDATA  <= wdata[1];
                      WSTRB  <= be[1];
                      WLAST  <= 1'b1;
                      WUSER  <= user;
                      WVALID <= 1'b1;
                      @(req_DW_granted);
                      WDATA      <= '0;
                      WSTRB      <= '0;
                      WLAST      <= '0;
                      WUSER      <= '0;
                      WVALID     <= '0;
              end
      endtask

      task ST24_DW;

              //AXI write data bus -------------- // USED// --------------
              input  [2:0][AXI4_WDATA_WIDTH-1:0] wdata;
              input  [2:0][AXI_NUMBYTES-1:0]     be;
              input  [AXI4_USER_WIDTH-1:0]       user;
              // ---------------------------------------------------------------


              begin
                      #(`SOD);
                      WDATA  <= wdata[0];
                      WSTRB  <= be[0];
                      WLAST  <= 1'b0;
                      WUSER  <= user;
                      WVALID <= 1'b1;
                      @(req_DW_granted);

                      WDATA  <= wdata[1];
                      WSTRB  <= be[1];
                      WLAST  <= 1'b0;
                      WUSER  <= user;
                      WVALID <= 1'b1;
                      @(req_DW_granted);

                      WDATA  <= wdata[2];
                      WSTRB  <= be[2];
                      WLAST  <= 1'b1;
                      WUSER  <= user;
                      WVALID <= 1'b1;
                      @(req_DW_granted);
                      WDATA      <= '0;
                      WSTRB      <= '0;
                      WLAST      <= '0;
                      WUSER      <= '0;
                      WVALID     <= '0;
              end
      endtask

      task ST32_DW;

              //AXI write data bus -------------- // USED// --------------
              input  [3:0][AXI4_WDATA_WIDTH-1:0] wdata;
              input  [3:0][AXI_NUMBYTES-1:0]     be;
              input  [AXI4_USER_WIDTH-1:0]       user;
              // ---------------------------------------------------------------


              begin
                      #(`SOD);
                      WDATA  <= wdata[0];
                      WSTRB  <= be[0];
                      WLAST  <= 1'b0;
                      WUSER  <= user;
                      WVALID <= 1'b1;
                      @(req_DW_granted);

                      WDATA  <= wdata[1];
                      WSTRB  <= be[1];
                      WLAST  <= 1'b0;
                      WUSER  <= user;
                      WVALID <= 1'b1;
                      @(req_DW_granted);

                      WDATA  <= wdata[2];
                      WSTRB  <= be[2];
                      WLAST  <= 1'b0;
                      WUSER  <= user;
                      WVALID <= 1'b1;
                      @(req_DW_granted);

                      WDATA  <= wdata[3];
                      WSTRB  <= be[3];
                      WLAST  <= 1'b1;
                      WUSER  <= user;
                      WVALID <= 1'b1;
                      @(req_DW_granted);
                      WDATA      <= '0;
                      WSTRB      <= '0;
                      WLAST      <= '0;
                      WUSER      <= '0;
                      WVALID     <= '0;
              end
      endtask



      task ST64_DW;

              //AXI write data bus -------------- // USED// --------------
              input  [7:0][AXI4_WDATA_WIDTH-1:0] wdata;
              input  [7:0][AXI_NUMBYTES-1:0]     be;
              input  [AXI4_USER_WIDTH-1:0]       user;
              // ---------------------------------------------------------------


              begin
                      #(`SOD);
                      WDATA  <= wdata[0];
                      WSTRB  <= be[0];
                      WLAST  <= 1'b0;
                      WUSER  <= user;
                      WVALID <= 1'b1;
                      @(req_DW_granted);

                      WDATA  <= wdata[1];
                      WSTRB  <= be[1];
                      WLAST  <= 1'b0;
                      WUSER  <= user;
                      WVALID <= 1'b1;
                      @(req_DW_granted);

                      WDATA  <= wdata[2];
                      WSTRB  <= be[2];
                      WLAST  <= 1'b0;
                      WUSER  <= user;
                      WVALID <= 1'b1;
                      @(req_DW_granted);

                      WDATA  <= wdata[3];
                      WSTRB  <= be[3];
                      WLAST  <= 1'b0;
                      WUSER  <= user;
                      WVALID <= 1'b1;
                      @(req_DW_granted);

                      WDATA  <= wdata[4];
                      WSTRB  <= be[4];
                      WLAST  <= 1'b0;
                      WUSER  <= user;
                      WVALID <= 1'b1;
                      @(req_DW_granted);

                      WDATA  <= wdata[5];
                      WSTRB  <= be[5];
                      WLAST  <= 1'b0;
                      WUSER  <= user;
                      WVALID <= 1'b1;
                      @(req_DW_granted);

                      WDATA  <= wdata[6];
                      WSTRB  <= be[6];
                      WLAST  <= 1'b0;
                      WUSER  <= user;
                      WVALID <= 1'b1;
                      @(req_DW_granted);

                      WDATA  <= wdata[7];
                      WSTRB  <= be[7];
                      WLAST  <= 1'b1;
                      WUSER  <= user;
                      WVALID <= 1'b1;
                      @(req_DW_granted);

                      WDATA      <= '0;
                      WSTRB      <= '0;
                      WLAST      <= '0;
                      WUSER      <= '0;
                      WVALID     <= '0;
              end
      endtask


      task ST256_DW;

              //AXI write data bus -------------- // USED// --------------
              input  [31:0][AXI4_WDATA_WIDTH-1:0] wdata;
              input  [31:0][AXI_NUMBYTES-1:0]     be;
              input  [AXI4_USER_WIDTH-1:0]        user;
              // ---------------------------------------------------------------
         int                                            burst_count;

              begin
                      #(`SOD);
                 for (burst_count=0;burst_count < 31;burst_count++) begin
                      WDATA  <= wdata[burst_count];
                      WSTRB  <= be[burst_count];
                      WLAST  <= 1'b0;
                      WUSER  <= user;
                      WVALID <= 1'b1;
                      @(req_DW_granted);
                 end

                      WDATA  <= wdata[31];
                      WSTRB  <= be[31];
                      WLAST  <= 1'b1;
                      WUSER  <= user;
                      WVALID <= 1'b1;
                      @(req_DW_granted);

                      WDATA      <= '0;
                      WSTRB      <= '0;
                      WLAST      <= '0;
                      WUSER      <= '0;
                      WVALID     <= '0;
              end
      endtask


      task LD4;
              input   [AXI4_ID_WIDTH-1:0]      id;
              input   [AXI4_ADDRESS_WIDTH-1:0] address;
              input   [AXI4_USER_WIDTH-1:0]    user;
              begin
                      #(`SOD);
                      ARID        <=  id;
                      ARADDR      <=  address;
                      ARLEN       <=  8'h00;
                      ARSIZE      <=  3'b010;
                      ARBURST     <=  2'b01;
                      ARLOCK      <= '0;
                      ARCACHE     <= '0;
                      ARPROT      <= '0;
                      ARREGION    <= '0;
                      ARUSER      <=  user;
                      ARQOS       <= '0;
                      ARVALID     <=  1'b1;
                      @(req_AR_granted);
                      ARID        <= '0;
                      ARADDR      <= '0;
                      ARLEN       <= '0;
                      ARSIZE      <= '0;
                      ARBURST     <= '0;
                      ARLOCK      <= '0;
                      ARCACHE     <= '0;
                      ARPROT      <= '0;
                      ARREGION    <= '0;
                      ARUSER      <= '0;
                      ARQOS       <= '0;
                      ARVALID     <= '0;
              end
      endtask

      task LD8;
              input   [AXI4_ID_WIDTH-1:0]      id;
              input   [AXI4_ADDRESS_WIDTH-1:0] address;
              input   [AXI4_USER_WIDTH-1:0]    user;
              begin
                      #(`SOD);
                      ARID        <=  id;
                      ARADDR      <=  address;
                      ARLEN       <=  8'h00;
                      ARSIZE      <=  3'b011;
                      ARBURST     <=  2'b01;
                      ARLOCK      <= '0;
                      ARCACHE     <= '0;
                      ARPROT      <= '0;
                      ARREGION    <= '0;
                      ARUSER      <=  user;
                      ARQOS       <= '0;
                      ARVALID     <=  1'b1;
                      @(req_AR_granted);
                      ARID        <= '0;
                      ARADDR      <= '0;
                      ARLEN       <= '0;
                      ARSIZE      <= '0;
                      ARBURST     <= '0;
                      ARLOCK      <= '0;
                      ARCACHE     <= '0;
                      ARPROT      <= '0;
                      ARREGION    <= '0;
                      ARUSER      <= '0;
                      ARQOS       <= '0;
                      ARVALID     <= '0;
              end
      endtask

      task LD16;
              input   [AXI4_ID_WIDTH-1:0]      id;
              input   [AXI4_ADDRESS_WIDTH-1:0] address;
              input   [AXI4_USER_WIDTH-1:0]    user;
              begin
                      #(`SOD);
                      ARID        <=  id;
                      ARADDR      <=  address;
                      ARLEN       <=  8'h01;
                      ARSIZE      <=  3'b011;
                      ARBURST     <=  2'b01;
                      ARLOCK      <= '0;
                      ARCACHE     <= '0;
                      ARPROT      <= '0;
                      ARREGION    <= '0;
                      ARUSER      <=  user;
                      ARQOS       <= '0;
                      ARVALID     <=  1'b1;
                      @(req_AR_granted);
                      ARID        <= '0;
                      ARADDR      <= '0;
                      ARLEN       <= '0;
                      ARSIZE      <= '0;
                      ARBURST     <= '0;
                      ARLOCK      <= '0;
                      ARCACHE     <= '0;
                      ARPROT      <= '0;
                      ARREGION    <= '0;
                      ARUSER      <= '0;
                      ARQOS       <= '0;
                      ARVALID     <= '0;
              end
      endtask

      task LD24;
              input   [AXI4_ID_WIDTH-1:0]      id;
              input   [AXI4_ADDRESS_WIDTH-1:0] address;
              input   [AXI4_USER_WIDTH-1:0]    user;
              begin
                      #(`SOD);
                      ARID        <=  id;
                      ARADDR      <=  address;
                      ARLEN       <=  8'h02;
                      ARSIZE      <=  3'b011;
                      ARBURST     <=  2'b01;
                      ARLOCK      <= '0;
                      ARCACHE     <= '0;
                      ARPROT      <= '0;
                      ARREGION    <= '0;
                      ARUSER      <=  user;
                      ARQOS       <= '0;
                      ARVALID     <=  1'b1;
                      @(req_AR_granted);
                      ARID        <= '0;
                      ARADDR      <= '0;
                      ARLEN       <= '0;
                      ARSIZE      <= '0;
                      ARBURST     <= '0;
                      ARLOCK      <= '0;
                      ARCACHE     <= '0;
                      ARPROT      <= '0;
                      ARREGION    <= '0;
                      ARUSER      <= '0;
                      ARQOS       <= '0;
                      ARVALID     <= '0;
              end
      endtask

      task LD32;
              input   [AXI4_ID_WIDTH-1:0]      id;
              input   [AXI4_ADDRESS_WIDTH-1:0] address;
              input   [AXI4_USER_WIDTH-1:0]    user;
              begin : LD_16_TASK
                      #(`SOD);
                      ARID        <=  id;
                      ARADDR      <=  address;
                      ARLEN       <=  8'h03;
                      ARSIZE      <=  3'b011;
                      ARBURST     <=  2'b01;
                      ARLOCK      <= '0;
                      ARCACHE     <= '0;
                      ARPROT      <= '0;
                      ARREGION    <= '0;
                      ARUSER      <=  user;
                      ARQOS       <= '0;
                      ARVALID     <=  1'b1;
                      @(req_AR_granted);
                      ARID        <= '0;
                      ARADDR      <= '0;
                      ARLEN       <= '0;
                      ARSIZE      <= '0;
                      ARBURST     <= '0;
                      ARLOCK      <= '0;
                      ARCACHE     <= '0;
                      ARPROT      <= '0;
                      ARREGION    <= '0;
                      ARUSER      <= '0;
                      ARQOS       <= '0;
                      ARVALID     <= '0;
              end
      endtask

      task LD64;
              input   [AXI4_ID_WIDTH-1:0]      id;
              input   [AXI4_ADDRESS_WIDTH-1:0] address;
              input   [AXI4_USER_WIDTH-1:0]    user;
              begin : LD_32_TASK
                      #(`SOD);
                      ARID        <=  id;
                      ARADDR      <=  address;
                      ARLEN       <=  8'h07;
                      ARSIZE      <=  3'b011;
                      ARBURST     <=  2'b01;
                      ARLOCK      <= '0;
                      ARCACHE     <= '0;
                      ARPROT      <= '0;
                      ARREGION    <= '0;
                      ARUSER      <=  user;
                      ARQOS       <= '0;
                      ARVALID     <=  1'b1;
                      @(req_AR_granted);
                      ARID        <= '0;
                      ARADDR      <= '0;
                      ARLEN       <= '0;
                      ARSIZE      <= '0;
                      ARBURST     <= '0;
                      ARLOCK      <= '0;
                      ARCACHE     <= '0;
                      ARPROT      <= '0;
                      ARREGION    <= '0;
                      ARUSER      <= '0;
                      ARQOS       <= '0;
                      ARVALID     <= '0;
              end
      endtask // LD64

      task LD256;
              input   [AXI4_ID_WIDTH-1:0]      id;
              input   [AXI4_ADDRESS_WIDTH-1:0] address;
              input   [AXI4_USER_WIDTH-1:0]    user;
              begin : LD_256_TASK
                      #(`SOD);
                      ARID        <=  id;
                      ARADDR      <=  address;
                      ARLEN       <=  8'h1F;
                      ARSIZE      <=  3'b011;
                      ARBURST     <=  2'b01;
                      ARLOCK      <= '0;
                      ARCACHE     <= '0;
                      ARPROT      <= '0;
                      ARREGION    <= '0;
                      ARUSER      <=  user;
                      ARQOS       <= '0;
                      ARVALID     <=  1'b1;
                      @(req_AR_granted);
                      ARID        <= '0;
                      ARADDR      <= '0;
                      ARLEN       <= '0;
                      ARSIZE      <= '0;
                      ARBURST     <= '0;
                      ARLOCK      <= '0;
                      ARCACHE     <= '0;
                      ARPROT      <= '0;
                      ARREGION    <= '0;
                      ARUSER      <= '0;
                      ARQOS       <= '0;
                      ARVALID     <= '0;
              end
      endtask

      task BARRIER_AW ;
      begin : AW_BARRIER_TASK
          Nop;
          @(AW_barrier_exit);
      end
      endtask

      task BARRIER_AR ;
      begin : AR_BARRIER_TASK
          Nop;
          @(AR_barrier_exit);
      end
      endtask