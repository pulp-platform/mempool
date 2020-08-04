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
    parameter int unsigned NumCores        = 1                         ,
    parameter int unsigned NumHives        = 1                         ,
    parameter int unsigned BankingFactor   = 1                         ,
    // TCDM
    parameter addr_t TCDMBaseAddr          = 32'b0                     ,
    // Boot address
    parameter logic [31:0] BootAddr        = 32'h0000_0000             ,
    // Dependent parameters. DO NOT CHANGE!
    parameter int unsigned NumTiles        = NumCores / NumCoresPerTile,
    parameter int unsigned NumBanks        = NumCores * BankingFactor  ,
    parameter int unsigned NumBanksPerTile = NumBanks / NumTiles       ,
    parameter int unsigned NumBanksPerHive = NumBanks / NumHives       ,
    parameter int unsigned TCDMAddrWidth   = TCDMAddrMemWidth + $clog2(NumBanksPerHive)
  ) (
    // Clock and reset
    input  logic                     clk_i,
    input  logic                     rst_ni,
    input  logic                     testmode_i,
    // Scan chain
    input  logic                     scan_enable_i,
    input  logic                     scan_data_i,
    output logic                     scan_data_o,
    // AXI Plugs for testbench
    output axi_req_t  [NumTiles-1:0] axi_mst_req_o,
    input  axi_resp_t [NumTiles-1:0] axi_mst_resp_i
  );

  /*****************
   *  Definitions  *
   *****************/

  localparam NumTilesPerHive = NumTiles / NumHives;

  typedef logic [$clog2(NumTiles)-1:0] tile_id_t                            ;
  typedef logic [$clog2(NumTilesPerHive)-1:0] hive_tile_id_t                ;
  typedef logic [TCDMAddrMemWidth + $clog2(NumBanksPerTile)-1:0] tile_addr_t;
  typedef logic [TCDMAddrWidth-1:0] tcdm_addr_t                             ;

  /***********
   *  Reset  *
   ***********/

  logic rst_n;
  rstgen_bypass i_rstgen (
    .clk_i           (clk_i       ),
    .rst_ni          (rst_ni      ),
    .rst_test_mode_ni(rst_ni      ),
    .test_mode_i     (testmode_i  ),
    .init_no         (/* Unused */),
    .rst_no          (rst_n       )
  );

  /***********
   *  Tiles  *
   ***********/

  // Data interface
  logic          [NumTiles-1:0][NumHives-1:0] tcdm_master_req_valid;
  logic          [NumTiles-1:0][NumHives-1:0] tcdm_master_req_ready;
  tcdm_addr_t    [NumTiles-1:0][NumHives-1:0] tcdm_master_req_tgt_addr;
  logic          [NumTiles-1:0][NumHives-1:0] tcdm_master_req_wen;
  tcdm_payload_t [NumTiles-1:0][NumHives-1:0] tcdm_master_req_wdata;
  strb_t         [NumTiles-1:0][NumHives-1:0] tcdm_master_req_be;
  tcdm_payload_t [NumTiles-1:0][NumHives-1:0] tcdm_master_resp_rdata;
  logic          [NumTiles-1:0][NumHives-1:0] tcdm_master_resp_valid;
  logic          [NumTiles-1:0][NumHives-1:0] tcdm_master_resp_ready;
  logic          [NumTiles-1:0][NumHives-1:0] tcdm_slave_req_valid;
  logic          [NumTiles-1:0][NumHives-1:0] tcdm_slave_req_ready;
  tile_addr_t    [NumTiles-1:0][NumHives-1:0] tcdm_slave_req_tgt_addr;
  hive_tile_id_t [NumTiles-1:0][NumHives-1:0] tcdm_slave_req_ini_addr;
  logic          [NumTiles-1:0][NumHives-1:0] tcdm_slave_req_wen;
  tcdm_payload_t [NumTiles-1:0][NumHives-1:0] tcdm_slave_req_wdata;
  strb_t         [NumTiles-1:0][NumHives-1:0] tcdm_slave_req_be;
  hive_tile_id_t [NumTiles-1:0][NumHives-1:0] tcdm_slave_resp_ini_addr;
  logic          [NumTiles-1:0][NumHives-1:0] tcdm_slave_resp_valid;
  logic          [NumTiles-1:0][NumHives-1:0] tcdm_slave_resp_ready;
  tcdm_payload_t [NumTiles-1:0][NumHives-1:0] tcdm_slave_resp_rdata;

  for (genvar t = 0; unsigned'(t) < NumTiles; t++) begin: gen_tiles
    mempool_tile #(
      .NumBanksPerTile(NumBanksPerTile),
      .NumTiles       (NumTiles       ),
      .NumHives       (NumHives       ),
      .NumBanks       (NumBanks       ),
      .TCDMBaseAddr   (TCDMBaseAddr   ),
      .BootAddr       (BootAddr       )
    ) i_tile (
      .clk_i                     (clk_i                          ),
      .rst_ni                    (rst_n                          ),
      .scan_enable_i             (scan_enable_i                  ),
      .scan_data_i               (/* Unconnected */              ),
      .scan_data_o               (/* Unconnected */              ),
      .tile_id_i                 (t[$clog2(NumTiles)-1:0]        ),
      // TCDM Master interfaces
      .tcdm_master_req_valid_o   (tcdm_master_req_valid[t]       ),
      .tcdm_master_req_tgt_addr_o(tcdm_master_req_tgt_addr[t]    ),
      .tcdm_master_req_wen_o     (tcdm_master_req_wen[t]         ),
      .tcdm_master_req_wdata_o   (tcdm_master_req_wdata[t]       ),
      .tcdm_master_req_be_o      (tcdm_master_req_be[t]          ),
      .tcdm_master_req_ready_i   (tcdm_master_req_ready[t]       ),
      .tcdm_master_resp_valid_i  (tcdm_master_resp_valid[t]      ),
      .tcdm_master_resp_ready_o  (tcdm_master_resp_ready[t]      ),
      .tcdm_master_resp_rdata_i  (tcdm_master_resp_rdata[t]      ),
      // TCDM banks interface
      .tcdm_slave_req_valid_i    (tcdm_slave_req_valid[t]        ),
      .tcdm_slave_req_ready_o    (tcdm_slave_req_ready[t]        ),
      .tcdm_slave_req_tgt_addr_i (tcdm_slave_req_tgt_addr[t]     ),
      .tcdm_slave_req_be_i       (tcdm_slave_req_be[t]           ),
      .tcdm_slave_req_wen_i      (tcdm_slave_req_wen[t]          ),
      .tcdm_slave_req_wdata_i    (tcdm_slave_req_wdata[t]        ),
      .tcdm_slave_req_ini_addr_i (tcdm_slave_req_ini_addr[t]     ),
      .tcdm_slave_resp_ini_addr_o(tcdm_slave_resp_ini_addr[t]    ),
      .tcdm_slave_resp_rdata_o   (tcdm_slave_resp_rdata[t]       ),
      .tcdm_slave_resp_valid_o   (tcdm_slave_resp_valid[t]       ),
      .tcdm_slave_resp_ready_i   (tcdm_slave_resp_ready[t]       ),
      // AXI interface
      .axi_mst_req_o             (axi_mst_req_o[t]               ),
      .axi_mst_resp_i            (axi_mst_resp_i[t]              ),
      // Instruction refill interface
      .refill_qaddr_o            (/* Not yet implemented */      ),
      .refill_qlen_o             (/* Not yet implemented */      ), // AXI signal
      .refill_qvalid_o           (/* Not yet implemented */      ),
      .refill_qready_i           (/* Not yet implemented */ 1'b0 ),
      .refill_pdata_i            (/* Not yet implemented */ '0   ),
      .refill_perror_i           (/* Not yet implemented */ '0   ),
      .refill_pvalid_i           (/* Not yet implemented */ 1'b0 ),
      .refill_plast_i            (/* Not yet implemented */ 1'b0 ),
      .refill_pready_o           (/* Not yet implemented */      )
    );
  end : gen_tiles

  /*******************
   *  Interconnects  *
   *******************/

  logic          [NumHives-1:0][NumHives-1:0][NumTilesPerHive-1:0] master_req_valid;
  logic          [NumHives-1:0][NumHives-1:0][NumTilesPerHive-1:0] master_req_ready;
  tcdm_addr_t    [NumHives-1:0][NumHives-1:0][NumTilesPerHive-1:0] master_req_tgt_addr;
  logic          [NumHives-1:0][NumHives-1:0][NumTilesPerHive-1:0] master_req_wen;
  tcdm_payload_t [NumHives-1:0][NumHives-1:0][NumTilesPerHive-1:0] master_req_wdata;
  strb_t         [NumHives-1:0][NumHives-1:0][NumTilesPerHive-1:0] master_req_be;
  tcdm_payload_t [NumHives-1:0][NumHives-1:0][NumTilesPerHive-1:0] master_resp_rdata;
  logic          [NumHives-1:0][NumHives-1:0][NumTilesPerHive-1:0] master_resp_valid;
  logic          [NumHives-1:0][NumHives-1:0][NumTilesPerHive-1:0] master_resp_ready;
  logic          [NumHives-1:0][NumHives-1:0][NumTilesPerHive-1:0] slave_req_valid;
  logic          [NumHives-1:0][NumHives-1:0][NumTilesPerHive-1:0] slave_req_ready;
  tile_addr_t    [NumHives-1:0][NumHives-1:0][NumTilesPerHive-1:0] slave_req_tgt_addr;
  hive_tile_id_t [NumHives-1:0][NumHives-1:0][NumTilesPerHive-1:0] slave_req_ini_addr;
  logic          [NumHives-1:0][NumHives-1:0][NumTilesPerHive-1:0] slave_req_wen;
  tcdm_payload_t [NumHives-1:0][NumHives-1:0][NumTilesPerHive-1:0] slave_req_wdata;
  strb_t         [NumHives-1:0][NumHives-1:0][NumTilesPerHive-1:0] slave_req_be;
  hive_tile_id_t [NumHives-1:0][NumHives-1:0][NumTilesPerHive-1:0] slave_resp_ini_addr;
  logic          [NumHives-1:0][NumHives-1:0][NumTilesPerHive-1:0] slave_resp_valid;
  logic          [NumHives-1:0][NumHives-1:0][NumTilesPerHive-1:0] slave_resp_ready;
  tcdm_payload_t [NumHives-1:0][NumHives-1:0][NumTilesPerHive-1:0] slave_resp_rdata;


  for (genvar ini = 0; ini < NumHives; ini++) begin: gen_intercos_ini_hive
    for (genvar tgt = 0; tgt < NumHives; tgt++) begin: gen_intercos_tgt_hive
      // Connections
      for (genvar tile = 0; tile < NumTilesPerHive; tile++) begin: gen_connections
        assign master_req_valid[ini][tgt][tile]                         = tcdm_master_req_valid[NumTilesPerHive*ini + tile][tgt]   ;
        assign master_req_tgt_addr[ini][tgt][tile]                      = tcdm_master_req_tgt_addr[NumTilesPerHive*ini + tile][tgt];
        assign master_req_wen[ini][tgt][tile]                           = tcdm_master_req_wen[NumTilesPerHive*ini + tile][tgt]     ;
        assign master_req_wdata[ini][tgt][tile]                         = tcdm_master_req_wdata[NumTilesPerHive*ini + tile][tgt]   ;
        assign master_req_be[ini][tgt][tile]                            = tcdm_master_req_be[NumTilesPerHive*ini + tile][tgt]      ;
        assign tcdm_master_req_ready[NumTilesPerHive*ini + tile][tgt]   = master_req_ready[ini][tgt][tile]                         ;
        assign tcdm_master_resp_valid[NumTilesPerHive*ini + tile][tgt]  = master_resp_valid[ini][tgt][tile]                        ;
        assign tcdm_master_resp_rdata[NumTilesPerHive*ini + tile][tgt]  = master_resp_rdata[ini][tgt][tile]                        ;
        assign master_resp_ready[ini][tgt][tile]                        = tcdm_master_resp_ready[NumTilesPerHive*ini + tile][tgt]  ;
        assign tcdm_slave_req_valid[NumTilesPerHive*tgt + tile][ini]    = slave_req_valid[ini][tgt][tile]                          ;
        assign tcdm_slave_req_tgt_addr[NumTilesPerHive*tgt + tile][ini] = slave_req_tgt_addr[ini][tgt][tile]                       ;
        assign tcdm_slave_req_ini_addr[NumTilesPerHive*tgt + tile][ini] = slave_req_ini_addr[ini][tgt][tile]                       ;
        assign tcdm_slave_req_wen[NumTilesPerHive*tgt + tile][ini]      = slave_req_wen[ini][tgt][tile]                            ;
        assign tcdm_slave_req_wdata[NumTilesPerHive*tgt + tile][ini]    = slave_req_wdata[ini][tgt][tile]                          ;
        assign tcdm_slave_req_be[NumTilesPerHive*tgt + tile][ini]       = slave_req_be[ini][tgt][tile]                             ;
        assign slave_req_ready[ini][tgt][tile]                          = tcdm_slave_req_ready[NumTilesPerHive*tgt + tile][ini]    ;
        assign slave_resp_valid[ini][tgt][tile]                         = tcdm_slave_resp_valid[NumTilesPerHive*tgt + tile][ini]   ;
        assign slave_resp_rdata[ini][tgt][tile]                         = tcdm_slave_resp_rdata[NumTilesPerHive*tgt + tile][ini]   ;
        assign slave_resp_ini_addr[ini][tgt][tile]                      = tcdm_slave_resp_ini_addr[NumTilesPerHive*tgt + tile][ini];
        assign tcdm_slave_resp_ready[NumTilesPerHive*tgt + tile][ini]   = slave_resp_ready[ini][tgt][tile]                         ;
      end: gen_connections

      // Interconnect
      variable_latency_interconnect #(
        .NumIn            (NumTilesPerHive                           ),
        .NumOut           (NumTilesPerHive                           ),
        .AddrWidth        (TCDMAddrWidth                             ),
        .DataWidth        ($bits(tcdm_payload_t)                     ),
        .BeWidth          (DataWidth/8                               ),
        .ByteOffWidth     (0                                         ),
        .AddrMemWidth     (TCDMAddrMemWidth + $clog2(NumBanksPerTile)),
        .Topology         (tcdm_interconnect_pkg::BFLY4              ),
        .SpillRegisterReq (64'b10                                    ),
        .SpillRegisterResp(64'b10                                    ),
        .AxiVldRdy        (1'b1                                      )
      ) i_interco (
        .clk_i          (clk_i                        ),
        .rst_ni         (rst_n                        ),
        .req_valid_i    (master_req_valid[ini][tgt]   ),
        .req_ready_o    (master_req_ready[ini][tgt]   ),
        .req_tgt_addr_i (master_req_tgt_addr[ini][tgt]),
        .req_wen_i      (master_req_wen[ini][tgt]     ),
        .req_wdata_i    (master_req_wdata[ini][tgt]   ),
        .req_be_i       (master_req_be[ini][tgt]      ),
        .resp_valid_o   (master_resp_valid[ini][tgt]  ),
        .resp_ready_i   (master_resp_ready[ini][tgt]  ),
        .resp_rdata_o   (master_resp_rdata[ini][tgt]  ),
        .req_valid_o    (slave_req_valid[ini][tgt]    ),
        .req_ready_i    (slave_req_ready[ini][tgt]    ),
        .req_be_o       (slave_req_be[ini][tgt]       ),
        .req_wdata_o    (slave_req_wdata[ini][tgt]    ),
        .req_wen_o      (slave_req_wen[ini][tgt]      ),
        .req_ini_addr_o (slave_req_ini_addr[ini][tgt] ),
        .req_tgt_addr_o (slave_req_tgt_addr[ini][tgt] ),
        .resp_ini_addr_i(slave_resp_ini_addr[ini][tgt]),
        .resp_rdata_i   (slave_resp_rdata[ini][tgt]   ),
        .resp_valid_i   (slave_resp_valid[ini][tgt]   ),
        .resp_ready_o   (slave_resp_ready[ini][tgt]   )
      );
    end
  end

  /****************
   *  Assertions  *
   ****************/

  if (NumCores > 1024)
    $fatal(1, "[mempool] MemPool is currently limited to 1024 cores.");

  if (NumTiles <= 1)
    $fatal(1, "[mempool] MemPool requires at least two tiles.");

  if (NumCores != NumTiles * NumCoresPerTile)
    $fatal(1, "[mempool] The number of cores is not divisible by the number of cores per tile.");

  if (BankingFactor < 1)
    $fatal(1, "[mempool] The banking factor must be a positive integer.");

  if (BankingFactor != 2**$clog2(BankingFactor))
    $fatal(1, "[mempool] The banking factor must be a power of two.");

endmodule : mempool
