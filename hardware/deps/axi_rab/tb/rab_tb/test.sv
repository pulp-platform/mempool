// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

`timescale 1ns/10ps
`include "pulp_soc_defines.sv"

import AXI4LITE_M::*;
import PACKET::*;
typedef bit [7:0]    bit8;
typedef bit [31:0]   bit32;

task bit32tobit8(bit32 in_data, output bit8 out_data[4] );
   out_data[0] = in_data[7:0];
   out_data[1] = in_data[15:8];
   out_data[2] = in_data[23:16];
   out_data[3] = in_data[31:24];
endtask // bit32tobit8

task slice_cfg(AXI4Lite_m_env axi4lite_intf, int unsigned slice_num, bit [31:0] low_addr, bit [31:0] high_addr, bit [31:0] offset, bit wen, bit ren, bit en);
   bit8 low_addr4[4], high_addr4[4], offset4[4], en4[4], wrRespOut[];
   int unsigned wrRespPtr;
   bit32tobit8(low_addr,low_addr4);
   bit32tobit8(high_addr,high_addr4);
   bit32tobit8(offset,offset4);
   bit32tobit8({29'h0,wen,ren,en},en4);

   axi4lite_intf.writeData(wrRespPtr, slice_num*32, low_addr4);
   axi4lite_intf.getWrResp(wrRespPtr, wrRespOut);
   axi4lite_intf.writeData(wrRespPtr, slice_num*32+8, high_addr4);
   axi4lite_intf.getWrResp(wrRespPtr, wrRespOut);
   axi4lite_intf.writeData(wrRespPtr, slice_num*32+16, offset4);
   axi4lite_intf.getWrResp(wrRespPtr, wrRespOut);
   axi4lite_intf.writeData(wrRespPtr, slice_num*32+24, en4);
   axi4lite_intf.getWrResp(wrRespPtr, wrRespOut);

endtask // slice_cfg

task slice_acp_cfg(AXI4Lite_m_env axi4lite_intf, int unsigned slice_num, bit [31:0] low_addr, bit [31:0] high_addr, bit [31:0] offset, bit wen, bit ren, bit en);
   bit8 low_addr4[4], high_addr4[4], offset4[4], en4[4], wrRespOut[];
   int unsigned wrRespPtr;
   bit32tobit8(low_addr,low_addr4);
   bit32tobit8(high_addr,high_addr4);
   bit32tobit8(offset,offset4);
   bit32tobit8({28'h0,1'b1,wen,ren,en},en4);

   axi4lite_intf.writeData(wrRespPtr, slice_num*32, low_addr4);
   axi4lite_intf.getWrResp(wrRespPtr, wrRespOut);
   axi4lite_intf.writeData(wrRespPtr, slice_num*32+8, high_addr4);
   axi4lite_intf.getWrResp(wrRespPtr, wrRespOut);
   axi4lite_intf.writeData(wrRespPtr, slice_num*32+16, offset4);
   axi4lite_intf.getWrResp(wrRespPtr, wrRespOut);
   axi4lite_intf.writeData(wrRespPtr, slice_num*32+24, en4);
   axi4lite_intf.getWrResp(wrRespPtr, wrRespOut);

endtask // slice_acp_cfg


task l2_cfg(AXI4Lite_m_env axi4lite_intf, string va_or_pa, int unsigned port_num, bit [31:0] ram_location, bit [31:0] data);
   bit8 data4[4],wrRespOut[];
   int unsigned wrRespPtr,axi_addr;
   bit32tobit8(data,data4);
   if(va_or_pa == "va") begin
      if(ram_location >1023) begin
         $error("Max ram location is 1023");
      end else begin
         axi_addr = (port_num+1)*16'h4000 + ram_location*4;
      end
   end else if(va_or_pa == "pa") begin
      if(ram_location >1023) begin
         $error("Max ram location is 1023");
      end else begin
         axi_addr = (port_num+1)*16'h4000 + (ram_location+1024)*4;
      end
   end
   axi4lite_intf.writeData(wrRespPtr, axi_addr, data4);
endtask // l2_cfg



program test
  #(
     parameter TEST_NAME = "reg_rd_wr",
     parameter A = 4,
     parameter integer A_ARRAY [3:0] = {10,20,30,40}
   );

   initial begin

      bit8 dataIn[], dataOut[], wrRespOut[], wrRespExp[], rdRespOut[], rdRespExp[];
      int unsigned address, wrRespPtr, rdPtr;
      int x,error_buf=0,i, data;

      Packet pkt = new();

      //
      AXI4Lite_m_env axi4lite_m;
      //  Create AXI Lite master
      axi4lite_m    = new("AXI master", rab_tb.axi4lite_m_if_0, 4);

      //   Start AXI Lite master vip
      axi4lite_m.startEnv();
      axi4lite_m.setRndDelay(0, 100, 0, 10);
      axi4lite_m.setTimeOut(10000, 100000);
      axi4lite_m.respReportMode(1);

      // Wait several clocks
      repeat (50) @(posedge rab_tb.clk_i);
      // The reset would have been released by now

      $display("Name of the test is %s",TEST_NAME);

      if(TEST_NAME == "reg_rd_wr") begin
         // Write to slice registers
         for (address=0; address < 32'h00000100; address+=4) begin
            pkt.genRndPkt(4, dataIn);
            pkt.PrintPkt("Data In", dataIn);
            $display("Data Length is %d bytes", dataIn.size());
            $display("Address is %h", address);
            axi4lite_m.writeData(wrRespPtr, address, dataIn);
            axi4lite_m.getWrResp(wrRespPtr, wrRespOut);
         end

         // Read slice registers
         for (address=0; address < 32'h00000100; address+=4) begin
            axi4lite_m.readData(address, dataIn.size(), rdPtr);
            axi4lite_m.getData(rdPtr, dataOut, rdRespOut);
         end
      end // if (TEST_NAME == "reg_rd_wr")

      if(TEST_NAME == "single_hit") begin
         slice_cfg(axi4lite_m, 1, 32'h00000000, 32'h000000f0, 32'h000, '1, '1, '1); // Configure Slice regs
         rab_tb.tgen2rab_fetch_en <= '1; // Start AXI transactions
         @(rab_tb.tgen2rab_eoc); // Wait till AXI transactions are completed
         repeat (10) @(posedge rab_tb.clk_i);
      end

      if(TEST_NAME == "multi_hit") begin

         slice_cfg(axi4lite_m, 1, 32'h10000000, 32'h20000000, 32'hF00000, '1, '1, '1);

         // L1
         slice_cfg(axi4lite_m, 2, 32'h00000010, 32'h000000f0, 32'h100, '1, '1, '1); // Configure Slice regs
         slice_cfg(axi4lite_m, 3, 32'h00000010, 32'h000000f4, 32'h200, '1, '1, '1); // Configure Slice regs
         slice_cfg(axi4lite_m, 4, 32'h00000010, 32'h000000f8, 32'h300, '1, '1, '1); // Configure Slice regs
         slice_cfg(axi4lite_m, 5, 32'h00000010, 32'h000000fc, 32'h400, '1, '1, '1); // Configure Slice regs

         // // Allow L1 multi hits
         // bit32tobit8(32'b10, dataIn);
         // axi4lite_m.writeData(wrRespPtr, 16, dataIn);
         // axi4lite_m.getWrResp(wrRespPtr, wrRespOut);

         // L2
         //Initialize RAMs to zero
         for (address = 0; address<1024; address++) begin
            l2_cfg(axi4lite_m, "va", 0, address, 0);
            l2_cfg(axi4lite_m, "pa", 0, address, 0);
         end

         // First entry per set
         for (i = 0; i<32; i++) begin
            address = 32*i;
            data = (i << 4) + 4'hF;
            l2_cfg(axi4lite_m, "va", 0, address, data);
            data = 32'hF00 + i;
            l2_cfg(axi4lite_m, "pa", 0, address, data);
         end

         // Second entry per set
         for (i = 0; i<32; i++) begin
            address = 32*i + 1;
            data = (i << 4) + 4'hF; // same VA -> multi_hit
            l2_cfg(axi4lite_m, "va", 0, address, data);
            data = 32'h1F00 + i;
            l2_cfg(axi4lite_m, "pa", 0, address, data);
         end

         // Third entry per set
         for (i = 0; i<32; i++) begin
            address = 32*i + 2;
            data = (i << 4) + 4'hF; // same VA -> multi_hit
            l2_cfg(axi4lite_m, "va", 0, address, data);
            data = 32'h2F00 + i;
            l2_cfg(axi4lite_m, "pa", 0, address, data);
         end

         // Fourth entry per set
         for (i = 0; i<32; i++) begin
            address = 32*i + 3;
            data = (i << 4) + 4'hF; // same VA -> multi_hit
            l2_cfg(axi4lite_m, "va", 0, address, data);
            data = 32'h2F00 + i;
            l2_cfg(axi4lite_m, "pa", 0, address, data);
         end

         // 17th entry of Set 0 - will be on Port 1
         address = 16;
         data    = (0 << 4) + 4'hF;
         l2_cfg(axi4lite_m, "va", 0, address, data);
         data = 32'hF00;
         l2_cfg(axi4lite_m, "pa", 0, address, data);

         rab_tb.tgen2rab_fetch_en <= '1; // Start AXI transactions
         @(rab_tb.tgen2rab_eoc); // Wait till AXI transactions are completed
         repeat (10) @(posedge rab_tb.clk_i);
      end

      if(TEST_NAME == "prot") begin
         slice_cfg(axi4lite_m, 1, 32'h00000000, 32'h000000f0, 32'h100, '1, '0, '0); // Configure Slice regs
         rab_tb.tgen2rab_fetch_en <= '1; // Start AXI transactions
         @(rab_tb.tgen2rab_eoc); // Wait till AXI transactions are completed
         repeat (10) @(posedge rab_tb.clk_i);
      end

      // Debugging scenariop from Zynq platform
      if(TEST_NAME == "l2_board") begin
         for (address = 0; address<1024; address++) begin
            l2_cfg(axi4lite_m, "va", 0, address, 0);
            l2_cfg(axi4lite_m, "pa", 0, address, 0);
         end
         l2_cfg(axi4lite_m, "va", 0, 32*8, 32'h003ec487);
         l2_cfg(axi4lite_m, "pa", 0, 32*8, 32'h0001d8e4);
         repeat (100) @(posedge rab_tb.clk_i);
         l2_cfg(axi4lite_m, "va", 0, 32*7, 32'h003ec497);
         l2_cfg(axi4lite_m, "pa", 0, 32*7, 32'h0001d8f1);
         repeat (100) @(posedge rab_tb.clk_i);
         rab_tb.tgen2rab_fetch_en <= '1; // Start AXI transactions
         @(rab_tb.tgen2rab_eoc); // Wait till AXI transactions are completed
         repeat (10) @(posedge rab_tb.clk_i);
      end

      // L2 TLB test
      if(TEST_NAME == "l2") begin
         //Initialize RAMs to zero
         for (address = 0; address<1024; address++) begin
            l2_cfg(axi4lite_m, "va", 0, address, 0);
            l2_cfg(axi4lite_m, "pa", 0, address, 0);
         end
         slice_cfg(axi4lite_m, 1, 32'h00001000, 32'h00002000, 32'hA000, '1, '1, '1); // Configure Slice regs
         slice_acp_cfg(axi4lite_m, 6, 32'h00007000, 32'h00008000, 32'hB000, '1, '1, '1); // Configure Slice regs
         //prot
         slice_cfg(axi4lite_m, 2, 32'h00002000, 32'h00003000, 32'hB000, '0, '0, '1); // Configure Slice regs
         // rab multi
         slice_cfg(axi4lite_m, 3, 32'h00005000, 32'h00006000, 32'hF000, '1, '1, '1); // Configure Slice regs
         slice_cfg(axi4lite_m, 4, 32'h00005000, 32'h00006000, 32'hF100, '1, '1, '1); // Configure Slice regs
         slice_cfg(axi4lite_m, 5, 32'h00005000, 32'h00006000, 32'hF200, '1, '1, '1); // Configure Slice regs

         l2_cfg(axi4lite_m, "va", .port_num(0), .ram_location(0), .data(32'h00000007)); // Page num=0
         l2_cfg(axi4lite_m, "va", 0, 32*4+31, 32'h00000047); // page num= 4
         l2_cfg(axi4lite_m, "pa", 0, 0, 32'h00000124);
         l2_cfg(axi4lite_m, "pa", 0, 32*4+31, 32'h00000ABC);
         //wen,ren = 0
         l2_cfg(axi4lite_m, "va", 0, 32*3+0, 32'h00000031); //page num = 3
         l2_cfg(axi4lite_m, "pa", 0, 32*3+0, 32'h0000048C);
         //L2 acp
         l2_cfg(axi4lite_m, "va", 0, 32*6+1, 32'h0000006F); // page num = 6
         l2_cfg(axi4lite_m, "pa", 0, 32*6+1, 32'h0000058C);
        // l2_cfg(axi4lite_m, "va", 0, 32*6+15, 32'h00000067); // page num = 6
        // l2_cfg(axi4lite_m, "pa", 0, 32*6+15, 32'h00000500);

         repeat (100) @(posedge rab_tb.clk_i);
         rab_tb.tgen2rab_fetch_en <= '1; // Start AXI transactions
         @(rab_tb.tgen2rab_eoc); // Wait till AXI transactions are completed
         repeat (10) @(posedge rab_tb.clk_i);
      end

      // Use all L2 entries
      if(TEST_NAME == "all_l2") begin
         for (address = 0; address<1024; address++) begin
            l2_cfg(axi4lite_m, "va", 0, address, 0);
            l2_cfg(axi4lite_m, "pa", 0, address, 0);
         end
         for (i = 0; i<32; i++) begin
            address = (32*i) + ((i%2)*31);
            data = (i << 4)+ 7;
            l2_cfg(axi4lite_m, "va", 0, address, data);
            data = i << 8;
            l2_cfg(axi4lite_m, "pa", 0, address, data);
         end
         repeat (4000) @(posedge rab_tb.clk_i);
         rab_tb.tgen2rab_fetch_en = '1; // Start AXI transactions
         @(rab_tb.tgen2rab_eoc); // Wait till AXI transactions are completed
         repeat (10) @(posedge rab_tb.clk_i);
      end

      if (TEST_NAME == "l1_and_l2" ) begin
         // init L2
         for (address = 0; address<1024; address++) begin
            l2_cfg(axi4lite_m, "va", 0, address, 0);
            l2_cfg(axi4lite_m, "pa", 0, address, 0);
         end

         // config L1
         slice_acp_cfg(axi4lite_m, 1, 32'h00000000, 32'h00001000, 32'hF00000, '1, '1, '1);
         slice_acp_cfg(axi4lite_m, 2, 32'h00001000, 32'h00002000, 32'hF01000, '1, '1, '1);
         slice_acp_cfg(axi4lite_m, 3, 32'h00003000, 32'h00004000, 32'hF03000, '1, '1, '1);

         slice_acp_cfg(axi4lite_m, 4, 32'h10000000, 32'h20000000, 32'hF00000, '1, '1, '1);

         // config L2
         // First entry per set
         for (i = 0; i<32; i++) begin
            address = 32*i;
            data = (i << 4) + 4'hF;
            l2_cfg(axi4lite_m, "va", 0, address, data);
            data = 32'hF00 + i;
            l2_cfg(axi4lite_m, "pa", 0, address, data);
         end

         // Last entry per set
         for (i = 0; i<32; i++) begin
            address = 32*i + 31;
            data = (i << 4) + 4'hF + (32 << 4); // next VA in same set
            l2_cfg(axi4lite_m, "va", 0, address, data);
            data = 32'h4F00 + i;
            l2_cfg(axi4lite_m, "pa", 0, address, data);
         end

         repeat (100) @(posedge rab_tb.clk_i);

         // start AXI transactions
         rab_tb.tgen2rab_fetch_en = '1;

         // wait for reconfig test phase
         wait (rab_tb.tgen2rab.ar_addr == 32'hF000);

         repeat (16) @(posedge rab_tb.clk_i);

         // re-config L2
         // Fifth entry per set
         i = 0;
         address = (32*i) + 4;
         data = (i << 4) + 4'hF + (2 << (4 + 5));
         l2_cfg(axi4lite_m, "va", 0, address, data);
         data = 32'h1F00 + i;
         l2_cfg(axi4lite_m, "pa", 0, address, data);

         repeat (16) @(posedge rab_tb.clk_i);

         i = 1;
         address = (32*i) + 4;
         data = (i << 4) + 4'hF + (2 << (4 + 5));
         l2_cfg(axi4lite_m, "va", 0, address, data);
         data = 32'h1F00 + i;
         l2_cfg(axi4lite_m, "pa", 0, address, data);

         // wait for completion
         @(rab_tb.tgen2rab_eoc);

         repeat (10) @(posedge rab_tb.clk_i);
      end

      if(TEST_NAME == "print") begin
         $display("Array size is %d. Elements are %d %d %d %d", A, A_ARRAY[0], A_ARRAY[1], A_ARRAY[2], A_ARRAY[3]);
         $display("Max element is %p",A_ARRAY.max);

      end // if (TEST_NAME == "print")

      repeat (50) @(posedge rab_tb.clk_i);


   // Make sure all buffers are empty
      if(rab_tb.addr_ptr != rab_tb.addr_check_ptr) begin
         $error("Input buffer not empty");
         error_buf+=1;
      end
      if(rab_tb.l1_ptr != rab_tb.l1_check_ptr) begin
         $error("L1 buffer not empty");
         error_buf+=1;
      end
      if(rab_tb.l2_ptr != rab_tb.l2_check_ptr) begin
         $error("L2 buffer not empty");
         error_buf+=1;
      end
      $display(".........1345..............");

      $display("Number of miss errors   = %10d",rab_tb.error_miss);
      $display("Number of errors        = %10d",rab_tb.error_num);
      $display("Number of buffer errors = %10d",error_buf);

   end // initial begin
endprogram // test
