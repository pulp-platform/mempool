// Copyright 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Michael Schaffner <schaffner@iis.ee.ethz.ch>, ETH Zurich
//         Matheus Cavalcante <matheusd@iis.ee.ethz.ch>, ETH Zurich
// Date: 06.03.2019
// Description: Synthesis wrapper for numa_interconnect without parameters

`include "defaults.svh"

module numa_interconnect_wrap (
    input  logic                                                         clk_i,
    input  logic                                                         rst_ni,
    // master side
    input  logic [`NUM_MASTER-1:0]                                       req_i,   // Request signal
    input  logic [`NUM_MASTER-1:0][`DATA_WIDTH-1:0]                      add_i,   // Address
    input  logic [`NUM_MASTER-1:0]                                       wen_i,   // 1: Store, 0: Load
    input  logic [`NUM_MASTER-1:0][`DATA_WIDTH-1:0]                      wdata_i, // Write data
    input  logic [`NUM_MASTER-1:0][`DATA_WIDTH/8-1:0]                    be_i,    // Byte enable
    output logic [`NUM_MASTER-1:0]                                       gnt_o,   // Grant signal
    output logic [`NUM_MASTER-1:0]                                       vld_o,   // Response valid, also asserted if write responses are enabled
    input  logic [`NUM_MASTER-1:0]                                       rdy_i,   // Response ready
    output logic [`NUM_MASTER-1:0][`DATA_WIDTH-1:0]                      rdata_o, // Data Response DATA (For LOAD commands)
    // slave side
    output logic [`NUM_MASTER * `BANK_FACT-1:0]                          req_o,   // Bank request
    output logic [`NUM_MASTER * `BANK_FACT-1:0][$clog2(`NUM_MASTER)-1:0] idx_o,   // Master index
    input  logic [`NUM_MASTER * `BANK_FACT-1:0]                          gnt_i,   // Bank grant
    output logic [`NUM_MASTER * `BANK_FACT-1:0][`MEM_ADDR_BITS-1:0]      add_o,   // Address
    output logic [`NUM_MASTER * `BANK_FACT-1:0]                          wen_o,   // 1: Store, 0: Load
    output logic [`NUM_MASTER * `BANK_FACT-1:0][`DATA_WIDTH-1:0]         wdata_o, // Write data
    output logic [`NUM_MASTER * `BANK_FACT-1:0][`DATA_WIDTH/8-1:0]       be_o,    // Byte enable
    input  logic [`NUM_MASTER * `BANK_FACT-1:0]                          vld_i,   // Valid response
    input  logic [`NUM_MASTER * `BANK_FACT-1:0][$clog2(`NUM_MASTER)-1:0] idx_i,   // Master index
    input  logic [`NUM_MASTER * `BANK_FACT-1:0][`DATA_WIDTH-1:0]         rdata_i  // Read data
  );

  if (`MUT_IMPL == 0) begin : gen_lic
    numa_interconnect #(
      .NumIn        ( `NUM_MASTER                ),
      .NumOut       ( `NUM_MASTER * `BANK_FACT   ),
      .AddrWidth    ( `DATA_WIDTH                ),
      .DataWidth    ( `DATA_WIDTH                ),
      .AddrMemWidth ( `MEM_ADDR_BITS             ),
      .Topology     ( tcdm_interconnect_pkg::LIC )
    ) i_numa_interconnect (
      .clk_i   ,
      .rst_ni  ,
      .req_i   ,
      .add_i   ,
      .wen_i   ,
      .wdata_i ,
      .be_i    ,
      .gnt_o   ,
      .vld_o   ,
      .rdy_i   ,
      .rdata_o ,
      .req_o   ,
      .idx_o   ,
      .gnt_i   ,
      .add_o   ,
      .wen_o   ,
      .wdata_o ,
      .be_o    ,
      .vld_i   ,
      .idx_i   ,
      .rdata_i
    );
  end else if (`MUT_IMPL == 1) begin : gen_bfly_r2
    numa_interconnect #(
      .NumIn        ( `NUM_MASTER                  ),
      .NumOut       ( `NUM_MASTER * `BANK_FACT     ),
      .AddrWidth    ( `DATA_WIDTH                  ),
      .DataWidth    ( `DATA_WIDTH                  ),
      .AddrMemWidth ( `MEM_ADDR_BITS               ),
      .Topology     ( tcdm_interconnect_pkg::BFLY2 )
    ) i_numa_interconnect (
      .clk_i   ,
      .rst_ni  ,
      .req_i   ,
      .add_i   ,
      .wen_i   ,
      .wdata_i ,
      .be_i    ,
      .gnt_o   ,
      .vld_o   ,
      .rdy_i   ,
      .rdata_o ,
      .req_o   ,
      .idx_o   ,
      .gnt_i   ,
      .add_o   ,
      .wen_o   ,
      .wdata_o ,
      .be_o    ,
      .vld_i   ,
      .idx_i   ,
      .rdata_i
    );
  end else if (`MUT_IMPL == 2) begin : gen_bfly_r4
    numa_interconnect #(
      .NumIn        ( `NUM_MASTER                  ),
      .NumOut       ( `NUM_MASTER * `BANK_FACT     ),
      .AddrWidth    ( `DATA_WIDTH                  ),
      .DataWidth    ( `DATA_WIDTH                  ),
      .AddrMemWidth ( `MEM_ADDR_BITS               ),
      .Topology     ( tcdm_interconnect_pkg::BFLY4 )
    ) i_numa_interconnect (
      .clk_i   ,
      .rst_ni  ,
      .req_i   ,
      .add_i   ,
      .wen_i   ,
      .wdata_i ,
      .be_i    ,
      .gnt_o   ,
      .vld_o   ,
      .rdy_i   ,
      .rdata_o ,
      .req_o   ,
      .idx_o   ,
      .gnt_i   ,
      .add_o   ,
      .wen_o   ,
      .wdata_o ,
      .be_o    ,
      .vld_i   ,
      .idx_i   ,
      .rdata_i
    );
  end 

endmodule : numa_interconnect_wrap
