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

module mempool #(
    parameter int unsigned NumCores         = 0                         ,
    parameter int unsigned NumCoresPerTile  = 0                         ,
    parameter int unsigned BankingFactor    = 0                         ,
    // TCDM
    parameter int unsigned TCDMSizePerBank  = 1024 /* [B] */            ,
    // Boot address
    parameter logic [31:0] BootAddr         = 32'h0000_0000             ,
    // AXI
    parameter type axi_aw_t                 = logic                     ,
    parameter type axi_w_t                  = logic                     ,
    parameter type axi_b_t                  = logic                     ,
    parameter type axi_ar_t                 = logic                     ,
    parameter type axi_r_t                  = logic                     ,
    parameter type axi_req_t                = logic                     ,
    parameter type axi_resp_t               = logic                     ,
    // Dependent parameters. DO NOT CHANGE!
    parameter int unsigned NumTiles         = NumCores / NumCoresPerTile,
    parameter int unsigned NumBanks         = NumCores * BankingFactor  ,
    parameter int unsigned NumBanksPerTile  = NumBanks / NumTiles       ,
    parameter int unsigned TCDMAddrMemWidth = $clog2(TCDMSizePerBank / BeWidth)
  ) (
    // Clock andreset
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

  /*****************
   *  Definitions  *
   *****************/

  typedef logic [$clog2(NumCores)-1:0] core_addr_t                          ;
  typedef logic [TCDMAddrMemWidth + $clog2(NumBanksPerTile)-1:0] tile_addr_t;

  /***********
   *  Tiles  *
   ***********/

  // Data interface

  logic       [NumCores-1:0] tcdm_master_req;
  logic       [NumCores-1:0] tcdm_master_gnt;
  logic       [NumCores-1:0] tcdm_master_rvalid;
  logic       [NumCores-1:0] tcdm_master_rready;
  addr_t      [NumCores-1:0] tcdm_master_addr;
  data_t      [NumCores-1:0] tcdm_master_rdata;
  logic       [NumCores-1:0] tcdm_master_wen;
  data_t      [NumCores-1:0] tcdm_master_wdata;
  strb_t      [NumCores-1:0] tcdm_master_be;
  logic       [NumCores-1:0] tcdm_slave_req;
  logic       [NumCores-1:0] tcdm_slave_gnt;
  tile_addr_t [NumCores-1:0] tcdm_slave_addr;
  core_addr_t [NumCores-1:0] tcdm_slave_ret_addr;
  core_addr_t [NumCores-1:0] tcdm_slave_resp_addr;
  logic       [NumCores-1:0] tcdm_slave_rvalid;
  data_t      [NumCores-1:0] tcdm_slave_rdata;
  logic       [NumCores-1:0] tcdm_slave_wen;
  data_t      [NumCores-1:0] tcdm_slave_wdata;
  strb_t      [NumCores-1:0] tcdm_slave_be;

  for (genvar t = 0; unsigned'(t) < NumTiles; t++) begin: gen_tiles

    mempool_tile #(
      .NumCoresPerTile(NumCoresPerTile),
      .NumBanksPerTile(NumBanksPerTile),
      .NumTiles       (NumTiles       ),
      .NumBanks       (NumBanks       ),
      .TCDMSizePerBank(TCDMSizePerBank),
      .BootAddr       (BootAddr       ),
      .axi_aw_t       (axi_aw_t       ),
      .axi_w_t        (axi_w_t        ),
      .axi_b_t        (axi_b_t        ),
      .axi_ar_t       (axi_ar_t       ),
      .axi_r_t        (axi_r_t        ),
      .axi_req_t      (axi_req_t      ),
      .axi_resp_t     (axi_resp_t     )
    ) tile (
      .clk_i              (clk_i                                                     ),
      .rst_ni             (rst_ni                                                    ),
      .scan_enable_i      (1'b0                                                      ),
      .scan_data_i        (1'b0                                                      ),
      .scan_data_o        (/* Unused */                                              ),
      .tile_id_i          (t                                                         ),
      // TCDM Master interfaces
      .tcdm_master_req_o  (tcdm_master_req[NumCoresPerTile*t +: NumCoresPerTile]     ),
      .tcdm_master_addr_o (tcdm_master_addr[NumCoresPerTile*t +: NumCoresPerTile]    ),
      .tcdm_master_wen_o  (tcdm_master_wen[NumCoresPerTile*t +: NumCoresPerTile]     ),
      .tcdm_master_wdata_o(tcdm_master_wdata[NumCoresPerTile*t +: NumCoresPerTile]   ),
      .tcdm_master_be_o   (tcdm_master_be[NumCoresPerTile*t +: NumCoresPerTile]      ),
      .tcdm_master_gnt_i  (tcdm_master_gnt[NumCoresPerTile*t +: NumCoresPerTile]     ),
      .tcdm_master_vld_i  (tcdm_master_rvalid[NumCoresPerTile*t +: NumCoresPerTile]  ),
      .tcdm_master_rdata_i(tcdm_master_rdata[NumCoresPerTile*t +: NumCoresPerTile]   ),
      // TCDM banks interface
      .mem_req_i          (tcdm_slave_req[NumCoresPerTile*t +: NumCoresPerTile]      ),
      .mem_ret_addr_i     (tcdm_slave_ret_addr[NumCoresPerTile*t +: NumCoresPerTile] ),
      .mem_gnt_o          (tcdm_slave_gnt[NumCoresPerTile*t +: NumCoresPerTile]      ),
      .mem_addr_i         (tcdm_slave_addr[NumCoresPerTile*t +: NumCoresPerTile]     ),
      .mem_wen_i          (tcdm_slave_wen[NumCoresPerTile*t +: NumCoresPerTile]      ),
      .mem_wdata_i        (tcdm_slave_wdata[NumCoresPerTile*t +: NumCoresPerTile]    ),
      .mem_be_i           (tcdm_slave_be[NumCoresPerTile*t +: NumCoresPerTile]       ),
      .mem_vld_o          (tcdm_slave_rvalid[NumCoresPerTile*t +: NumCoresPerTile]   ),
      .mem_resp_addr_o    (tcdm_slave_resp_addr[NumCoresPerTile*t +: NumCoresPerTile]),
      .mem_rdata_o        (tcdm_slave_rdata[NumCoresPerTile*t +: NumCoresPerTile]    ),
      // AXI interface
      .axi_mst_req_o      (axi_mst_req_o[t]                                          ),
      .axi_mst_resp_i     (axi_mst_resp_i[t]                                         ),
      // Instruction refill interface
      .refill_qaddr_o     (/* Not yet implemented */                                 ),
      .refill_qlen_o      (/* Not yet implemented */                                 ), // AXI signal
      .refill_qvalid_o    (/* Not yet implemented */                                 ),
      .refill_qready_i    (/* Not yet implemented */ 1'b0                            ),
      .refill_pdata_i     (/* Not yet implemented */ '0                              ),
      .refill_perror_i    (/* Not yet implemented */ '0                              ),
      .refill_pvalid_i    (/* Not yet implemented */ 1'b0                            ),
      .refill_plast_i     (/* Not yet implemented */ 1'b0                            ),
      .refill_pready_o    (/* Not yet implemented */                                 )
    );

    // The TCDM master port is always ready to accept the responses
    assign tcdm_master_rready[NumCoresPerTile*t +: NumCoresPerTile] = '1;

  end : gen_tiles

  /******************
   *  Interconnect  *
   ******************/

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
    .clk_i  (clk_i               ),
    .rst_ni (rst_ni              ),
    .req_i  (tcdm_master_req     ),
    .add_i  (tcdm_master_addr    ),
    .wen_i  (tcdm_master_wen     ),
    .wdata_i(tcdm_master_wdata   ),
    .be_i   (tcdm_master_be      ),
    .gnt_o  (tcdm_master_gnt     ),
    .vld_o  (tcdm_master_rvalid  ),
    .rdy_i  (tcdm_master_rready  ),
    .rdata_o(tcdm_master_rdata   ),
    .req_o  (tcdm_slave_req      ),
    .gnt_i  (tcdm_slave_gnt      ),
    .idx_o  (tcdm_slave_ret_addr ),
    .add_o  (tcdm_slave_addr     ),
    .wen_o  (tcdm_slave_wen      ),
    .wdata_o(tcdm_slave_wdata    ),
    .be_o   (tcdm_slave_be       ),
    .vld_i  (tcdm_slave_rvalid   ),
    .idx_i  (tcdm_slave_resp_addr),
    .rdata_i(tcdm_slave_rdata    )
  );

  /****************
   *  Assertions  *
   ****************/

  `ifndef SYNTHESIS
  `ifndef VERILATOR
  if (NumCores > 1024)
    $fatal(1, "[mempool] MemPool is currently limited to 1024 cores.");

  if (NumCores != NumTiles * NumCoresPerTile)
    $fatal(1, "[mempool] The number of cores is not divisible by the number of cores per tile.");

  if (BankingFactor < 1)
    $fatal(1, "[mempool] The banking factor must be a positive integer.");

  if (BankingFactor != 2**$clog2(BankingFactor))
    $fatal(1, "[mempool] The banking factor must be a power of two.");
  `endif
  `endif

endmodule : mempool
