// Copyright 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

import mempool_pkg::*;

module mempool_cluster #(
    // Boot address
    parameter logic [31:0] BootAddr = 32'h0000_0000
  ) (
    // Clock and reset
    input  logic                     clk_i ,
    input  logic                     rst_ni ,
    // AXI Plugs for testbench
    output axi_req_t  [NumTiles-1:0] axi_mst_req_o ,
    input  axi_resp_t [NumTiles-1:0] axi_mst_resp_i,
    // Scan chain
    input  logic                     scan_enable_i ,
    input  logic                     scan_data_i ,
    output logic                     scan_data_o
  );

  /***********
   *  Tiles  *
   ***********/

  // Data interface

  logic  [NumCores-1:0] tcdm_master_req;
  logic  [NumCores-1:0] tcdm_master_gnt;
  logic  [NumCores-1:0] tcdm_master_rvalid;
  logic  [NumCores-1:0] tcdm_master_rready;
  addr_t [NumCores-1:0] tcdm_master_addr;
  data_t [NumCores-1:0] tcdm_master_rdata;
  logic  [NumCores-1:0] tcdm_master_wen;
  data_t [NumCores-1:0] tcdm_master_wdata;
  be_t   [NumCores-1:0] tcdm_master_be;

  logic       [NumCores-1:0] tcdm_slave_req;
  logic       [NumCores-1:0] tcdm_slave_gnt;
  tile_addr_t [NumCores-1:0] tcdm_slave_addr;
  core_addr_t [NumCores-1:0] tcdm_slave_ret_addr;
  core_addr_t [NumCores-1:0] tcdm_slave_resp_addr;
  logic       [NumCores-1:0] tcdm_slave_rvalid;
  data_t      [NumCores-1:0] tcdm_slave_rdata;
  logic       [NumCores-1:0] tcdm_slave_wen;
  data_t      [NumCores-1:0] tcdm_slave_wdata;
  be_t        [NumCores-1:0] tcdm_slave_be;

  for (genvar t = 0; unsigned'(t) < NumTiles; t++) begin: gen_tiles

    tile #(
      .BootAddr ( BootAddr )
    ) tile (
      .clk_i              ( clk_i                                                      ),
      .rst_ni             ( rst_ni                                                     ),
      .scan_enable_i      ( 1'b0                                                       ),
      .scan_data_i        ( 1'b0                                                       ),
      .scan_data_o        (                                                            ),
      .tile_id_i          ( t                                                          ),
      // TCDM Master interfaces
      .tcdm_master_req_o  ( tcdm_master_req[NumCoresPerTile*t +: NumCoresPerTile]      ),
      .tcdm_master_addr_o ( tcdm_master_addr[NumCoresPerTile*t +: NumCoresPerTile]     ),
      .tcdm_master_wen_o  ( tcdm_master_wen[NumCoresPerTile*t +: NumCoresPerTile]      ),
      .tcdm_master_wdata_o( tcdm_master_wdata[NumCoresPerTile*t +: NumCoresPerTile]    ),
      .tcdm_master_be_o   ( tcdm_master_be[NumCoresPerTile*t +: NumCoresPerTile]       ),
      .tcdm_master_gnt_i  ( tcdm_master_gnt[NumCoresPerTile*t +: NumCoresPerTile]      ),
      .tcdm_master_vld_i  ( tcdm_master_rvalid[NumCoresPerTile*t +: NumCoresPerTile]   ),
      .tcdm_master_rdata_i( tcdm_master_rdata[NumCoresPerTile*t +: NumCoresPerTile]    ),
      // TCDM banks interface
      .mem_req_i          ( tcdm_slave_req[NumCoresPerTile*t +: NumCoresPerTile]       ),
      .mem_ret_addr_i     ( tcdm_slave_ret_addr[NumCoresPerTile*t +: NumCoresPerTile]  ),
      .mem_gnt_o          ( tcdm_slave_gnt[NumCoresPerTile*t +: NumCoresPerTile]       ),
      .mem_addr_i         ( tcdm_slave_addr[NumCoresPerTile*t +: NumCoresPerTile]      ),
      .mem_wen_i          ( tcdm_slave_wen[NumCoresPerTile*t +: NumCoresPerTile]       ),
      .mem_wdata_i        ( tcdm_slave_wdata[NumCoresPerTile*t +: NumCoresPerTile]     ),
      .mem_be_i           ( tcdm_slave_be[NumCoresPerTile*t +: NumCoresPerTile]        ),
      .mem_vld_o          ( tcdm_slave_rvalid[NumCoresPerTile*t +: NumCoresPerTile]    ),
      .mem_resp_addr_o    ( tcdm_slave_resp_addr[NumCoresPerTile*t +: NumCoresPerTile] ),
      .mem_rdata_o        ( tcdm_slave_rdata[NumCoresPerTile*t +: NumCoresPerTile]     ),
      // AXI interface
      .axi_mst_req_o      ( axi_mst_req_o[t]                                           ),
      .axi_mst_resp_i     ( axi_mst_resp_i[t]                                          ),
      // Instruction refill interface
      .refill_qaddr_o     ( /* Not yet implemented */                                  ),
      .refill_qlen_o      ( /* Not yet implemented */                                  ), // AXI signal
      .refill_qvalid_o    ( /* Not yet implemented */                                  ),
      .refill_qready_i    ( /* Not yet implemented */ 1'b0                             ),
      .refill_pdata_i     ( /* Not yet implemented */ '0                               ),
      .refill_perror_i    ( /* Not yet implemented */ '0                               ),
      .refill_pvalid_i    ( /* Not yet implemented */ 1'b0                             ),
      .refill_plast_i     ( /* Not yet implemented */ 1'b0                             ),
      .refill_pready_o    ( /* Not yet implemented */                                  )
    );

    // The TCDM master port is always ready to accept the responses
    assign tcdm_master_rready[NumCoresPerTile*t +: NumCoresPerTile] = '1;

  end : gen_tiles

  /***********************
   *  TCDM Interconnect  *
   ***********************/

  // Interconnect
  numa_interconnect #(
    .NumIn         (NumCores                                  ),
    .NumOut        (NumCores                                  ),
    .AddrWidth     (AddrWidth                                 ),
    .DataWidth     (DataWidth                                 ),
    .AddrMemWidth  (TCDMAddrMemWidth + $clog2(NumBanksPerTile)),
    .NumOutstanding(2                                         ),
    .WriteRespOn   (1'b0                                      ),
    .Topology      (tcdm_interconnect_pkg::BFLY4              )
  ) interco (
    .clk_i  (clk_i                ),
    .rst_ni (rst_ni               ),
    .req_i  (tcdm_master_req      ),
    .add_i  (tcdm_master_addr     ),
    .wen_i  (tcdm_master_wen      ),
    .wdata_i(tcdm_master_wdata    ),
    .be_i   (tcdm_master_be       ),
    .gnt_o  (tcdm_master_gnt      ),
    .vld_o  (tcdm_master_rvalid   ),
    .rdy_i  (tcdm_master_rready   ),
    .rdata_o(tcdm_master_rdata    ),
    .req_o  (tcdm_slave_req       ),
    .gnt_i  (tcdm_slave_gnt       ),
    .idx_o  (tcdm_slave_ret_addr  ),
    .add_o  (tcdm_slave_addr      ),
    .wen_o  (tcdm_slave_wen       ),
    .wdata_o(tcdm_slave_wdata     ),
    .be_o   (tcdm_slave_be        ),
    .vld_i  (tcdm_slave_rvalid    ),
    .idx_i  (tcdm_slave_resp_addr ),
    .rdata_i(tcdm_slave_rdata     )
  );

  /****************
   *  Assertions  *
   ****************/

  `ifndef SYNTHESIS
  initial begin
    core_cnt: assert (NumTiles <= 1024) else
      $fatal(1, "MemPool is currently limited to 1024 cores.");
  end
  `endif

endmodule : mempool_cluster
