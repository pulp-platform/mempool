// Copyright 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.


module mempool_group
  import mempool_pkg::*;
  import cf_math_pkg::idx_width;
#(
    parameter int unsigned NumBanksPerTile  = 1,
    parameter int unsigned NumTiles         = 1,
    parameter int unsigned NumBanks         = 1,
    parameter int unsigned NumCoresPerGroup = 1,
    // TCDM
    parameter addr_t TCDMBaseAddr           = 32'b0,
    parameter type tcdm_master_req_t        = logic,
    parameter type tcdm_master_resp_t       = logic,
    parameter type tcdm_slave_req_t         = logic,
    parameter type tcdm_slave_resp_t        = logic,
    // Boot address
    parameter logic [31:0] BootAddr         = 32'h0000_1000,
    // Dependant parameters. DO NOT CHANGE!
    parameter int unsigned NumTilesPerGroup = NumTiles / NumGroups
  ) (
    // Clock and reset
    input  logic                                         clk_i,
    input  logic                                         rst_ni,
    // Scan chain
    input  logic                                         scan_enable_i,
    input  logic                                         scan_data_i,
    output logic                                         scan_data_o,
    // Group ID
    input  logic              [idx_width(NumGroups)-1:0] group_id_i,
    // TCDM Master interfaces
    output tcdm_slave_req_t   [NumTilesPerGroup-1:0]     tcdm_master_north_req_o,
    output logic              [NumTilesPerGroup-1:0]     tcdm_master_north_req_valid_o,
    input  logic              [NumTilesPerGroup-1:0]     tcdm_master_north_req_ready_i,
    input  tcdm_master_resp_t [NumTilesPerGroup-1:0]     tcdm_master_north_resp_i,
    input  logic              [NumTilesPerGroup-1:0]     tcdm_master_north_resp_valid_i,
    output logic              [NumTilesPerGroup-1:0]     tcdm_master_north_resp_ready_o,
    output tcdm_slave_req_t   [NumTilesPerGroup-1:0]     tcdm_master_northeast_req_o,
    output logic              [NumTilesPerGroup-1:0]     tcdm_master_northeast_req_valid_o,
    input  logic              [NumTilesPerGroup-1:0]     tcdm_master_northeast_req_ready_i,
    input  tcdm_master_resp_t [NumTilesPerGroup-1:0]     tcdm_master_northeast_resp_i,
    input  logic              [NumTilesPerGroup-1:0]     tcdm_master_northeast_resp_valid_i,
    output logic              [NumTilesPerGroup-1:0]     tcdm_master_northeast_resp_ready_o,
    output tcdm_slave_req_t   [NumTilesPerGroup-1:0]     tcdm_master_east_req_o,
    output logic              [NumTilesPerGroup-1:0]     tcdm_master_east_req_valid_o,
    input  logic              [NumTilesPerGroup-1:0]     tcdm_master_east_req_ready_i,
    input  tcdm_master_resp_t [NumTilesPerGroup-1:0]     tcdm_master_east_resp_i,
    input  logic              [NumTilesPerGroup-1:0]     tcdm_master_east_resp_valid_i,
    output logic              [NumTilesPerGroup-1:0]     tcdm_master_east_resp_ready_o,
    // TCDM Slave interfaces
    input  tcdm_slave_req_t   [NumTilesPerGroup-1:0]     tcdm_slave_north_req_i,
    input  logic              [NumTilesPerGroup-1:0]     tcdm_slave_north_req_valid_i,
    output logic              [NumTilesPerGroup-1:0]     tcdm_slave_north_req_ready_o,
    output tcdm_master_resp_t [NumTilesPerGroup-1:0]     tcdm_slave_north_resp_o,
    output logic              [NumTilesPerGroup-1:0]     tcdm_slave_north_resp_valid_o,
    input  logic              [NumTilesPerGroup-1:0]     tcdm_slave_north_resp_ready_i,
    input  tcdm_slave_req_t   [NumTilesPerGroup-1:0]     tcdm_slave_northeast_req_i,
    input  logic              [NumTilesPerGroup-1:0]     tcdm_slave_northeast_req_valid_i,
    output logic              [NumTilesPerGroup-1:0]     tcdm_slave_northeast_req_ready_o,
    output tcdm_master_resp_t [NumTilesPerGroup-1:0]     tcdm_slave_northeast_resp_o,
    output logic              [NumTilesPerGroup-1:0]     tcdm_slave_northeast_resp_valid_o,
    input  logic              [NumTilesPerGroup-1:0]     tcdm_slave_northeast_resp_ready_i,
    input  tcdm_slave_req_t   [NumTilesPerGroup-1:0]     tcdm_slave_east_req_i,
    input  logic              [NumTilesPerGroup-1:0]     tcdm_slave_east_req_valid_i,
    output logic              [NumTilesPerGroup-1:0]     tcdm_slave_east_req_ready_o,
    output tcdm_master_resp_t [NumTilesPerGroup-1:0]     tcdm_slave_east_resp_o,
    output logic              [NumTilesPerGroup-1:0]     tcdm_slave_east_resp_valid_o,
    input  logic              [NumTilesPerGroup-1:0]     tcdm_slave_east_resp_ready_i,
    // Wake up interface
    input  logic              [NumCoresPerGroup-1:0]     wake_up_i 
  );

  /*****************
   *  Definitions  *
   *****************/

  localparam NumBanksPerGroup = NumBanks / NumGroups;
  localparam TCDMAddrWidth    = TCDMAddrMemWidth + idx_width(NumBanksPerGroup);

  typedef logic [idx_width(NumTiles)-1:0] tile_id_t;
  typedef logic [idx_width(NumTilesPerGroup)-1:0] tile_group_id_t;
  typedef logic [TCDMAddrMemWidth + idx_width(NumBanksPerTile)-1:0] tile_addr_t;
  typedef logic [TCDMAddrWidth-1:0] tcdm_addr_t;

  localparam int unsigned idx_east[16]  = (NumTilesPerGroup == 16) ? {0,2,8,10,1,3,9,11,4,6,12,14,5,7,13,15} : {0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15};
  localparam int unsigned idx_north[16] = (NumTilesPerGroup == 16) ? {0,1,4,5,2,3,6,7,8,9,12,13,10,11,14,15} : {0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15};

  /***********
   *  Tiles  *
   ***********/

  // TCDM interfaces
  // North
  tcdm_master_req_t  [NumTiles-1:0] tcdm_master_north_req;
  logic              [NumTiles-1:0] tcdm_master_north_req_valid;
  logic              [NumTiles-1:0] tcdm_master_north_req_ready;
  tcdm_slave_resp_t  [NumTiles-1:0] tcdm_slave_north_resp;
  logic              [NumTiles-1:0] tcdm_slave_north_resp_valid;
  logic              [NumTiles-1:0] tcdm_slave_north_resp_ready;
  // East
  tcdm_master_req_t  [NumTiles-1:0] tcdm_master_east_req;
  logic              [NumTiles-1:0] tcdm_master_east_req_valid;
  logic              [NumTiles-1:0] tcdm_master_east_req_ready;
  tcdm_slave_resp_t  [NumTiles-1:0] tcdm_slave_east_resp;
  logic              [NumTiles-1:0] tcdm_slave_east_resp_valid;
  logic              [NumTiles-1:0] tcdm_slave_east_resp_ready;
  // Northeast
  tcdm_master_req_t  [NumTiles-1:0] tcdm_master_northeast_req;
  logic              [NumTiles-1:0] tcdm_master_northeast_req_valid;
  logic              [NumTiles-1:0] tcdm_master_northeast_req_ready;
  tcdm_slave_resp_t  [NumTiles-1:0] tcdm_slave_northeast_resp;
  logic              [NumTiles-1:0] tcdm_slave_northeast_resp_valid;
  logic              [NumTiles-1:0] tcdm_slave_northeast_resp_ready;
  // Center
  tcdm_master_req_t  [NumTiles-1:0] tcdm_master_local_req;
  logic              [NumTiles-1:0] tcdm_master_local_req_valid;
  logic              [NumTiles-1:0] tcdm_master_local_req_ready;
  tcdm_master_resp_t [NumTiles-1:0] tcdm_master_local_resp;
  logic              [NumTiles-1:0] tcdm_master_local_resp_valid;
  logic              [NumTiles-1:0] tcdm_master_local_resp_ready;
  tcdm_slave_req_t   [NumTiles-1:0] tcdm_slave_local_req;
  logic              [NumTiles-1:0] tcdm_slave_local_req_valid;
  logic              [NumTiles-1:0] tcdm_slave_local_req_ready;
  tcdm_slave_resp_t  [NumTiles-1:0] tcdm_slave_local_resp;
  logic              [NumTiles-1:0] tcdm_slave_local_resp_valid;
  logic              [NumTiles-1:0] tcdm_slave_local_resp_ready;

  for (genvar t = 0; unsigned'(t) < NumTilesPerGroup; t++) begin: gen_tiles
    tile_id_t id;
    assign id = (group_id_i << $clog2(NumTilesPerGroup)) | t[idx_width(NumTilesPerGroup)-1:0];
    mempool_tile_wrap #(
      .NumBanksPerTile   (NumBanksPerTile   ),
      .NumTiles          (NumTiles          ),
      .NumBanks          (NumBanks          ),
      .TCDMBaseAddr      (TCDMBaseAddr      ),
      .BootAddr          (BootAddr          ),
      .tcdm_master_req_t (tcdm_master_req_t ),
      .tcdm_master_resp_t(tcdm_master_resp_t),
      .tcdm_slave_req_t  (tcdm_slave_req_t  ),
      .tcdm_slave_resp_t (tcdm_slave_resp_t )
    ) i_tile (
      .clk_i                             (clk_i                                       ),
      .rst_ni                            (rst_ni                                      ),
      .scan_enable_i                     (scan_enable_i                               ),
      .scan_data_i                       (/* Unconnected */                           ),
      .scan_data_o                       (/* Unconnected */                           ),
      .tile_id_i                         (id                                          ),
      // TCDM Master interfaces
      .tcdm_master_north_req_o           (tcdm_master_north_req[idx_north[t]]         ),
      .tcdm_master_north_req_valid_o     (tcdm_master_north_req_valid[idx_north[t]]   ),
      .tcdm_master_north_req_ready_i     (tcdm_master_north_req_ready[idx_north[t]]   ),
      .tcdm_master_north_resp_i          (tcdm_master_north_resp_i[idx_north[t]]      ),
      .tcdm_master_north_resp_valid_i    (tcdm_master_north_resp_valid_i[idx_north[t]]),
      .tcdm_master_north_resp_ready_o    (tcdm_master_north_resp_ready_o[idx_north[t]]),
      .tcdm_master_east_req_o            (tcdm_master_east_req[idx_east[t]]           ),
      .tcdm_master_east_req_valid_o      (tcdm_master_east_req_valid[idx_east[t]]     ),
      .tcdm_master_east_req_ready_i      (tcdm_master_east_req_ready[idx_east[t]]     ),
      .tcdm_master_east_resp_i           (tcdm_master_east_resp_i[idx_east[t]]        ),
      .tcdm_master_east_resp_valid_i     (tcdm_master_east_resp_valid_i[idx_east[t]]  ),
      .tcdm_master_east_resp_ready_o     (tcdm_master_east_resp_ready_o[idx_east[t]]  ),
      .tcdm_master_northeast_req_o       (tcdm_master_northeast_req[t]                ),
      .tcdm_master_northeast_req_valid_o (tcdm_master_northeast_req_valid[t]          ),
      .tcdm_master_northeast_req_ready_i (tcdm_master_northeast_req_ready[t]          ),
      .tcdm_master_northeast_resp_i      (tcdm_master_northeast_resp_i[t]             ),
      .tcdm_master_northeast_resp_valid_i(tcdm_master_northeast_resp_valid_i[t]       ),
      .tcdm_master_northeast_resp_ready_o(tcdm_master_northeast_resp_ready_o[t]       ),
      .tcdm_master_local_req_o           (tcdm_master_local_req[t]                    ),
      .tcdm_master_local_req_valid_o     (tcdm_master_local_req_valid[t]              ),
      .tcdm_master_local_req_ready_i     (tcdm_master_local_req_ready[t]              ),
      .tcdm_master_local_resp_i          (tcdm_master_local_resp[t]                   ),
      .tcdm_master_local_resp_valid_i    (tcdm_master_local_resp_valid[t]             ),
      .tcdm_master_local_resp_ready_o    (tcdm_master_local_resp_ready[t]             ),
      // TCDM banks interface
      .tcdm_slave_north_req_i            (tcdm_slave_north_req_i[t]                   ),
      .tcdm_slave_north_req_valid_i      (tcdm_slave_north_req_valid_i[t]             ),
      .tcdm_slave_north_req_ready_o      (tcdm_slave_north_req_ready_o[t]             ),
      .tcdm_slave_north_resp_o           (tcdm_slave_north_resp[idx_north[t]]         ),
      .tcdm_slave_north_resp_valid_o     (tcdm_slave_north_resp_valid[idx_north[t]]   ),
      .tcdm_slave_north_resp_ready_i     (tcdm_slave_north_resp_ready[idx_north[t]]   ),
      .tcdm_slave_east_req_i             (tcdm_slave_east_req_i[t]                    ),
      .tcdm_slave_east_req_valid_i       (tcdm_slave_east_req_valid_i[t]              ),
      .tcdm_slave_east_req_ready_o       (tcdm_slave_east_req_ready_o[t]              ),
      .tcdm_slave_east_resp_o            (tcdm_slave_east_resp[idx_east[t]]           ),
      .tcdm_slave_east_resp_valid_o      (tcdm_slave_east_resp_valid[idx_east[t]]     ),
      .tcdm_slave_east_resp_ready_i      (tcdm_slave_east_resp_ready[idx_east[t]]     ),
      .tcdm_slave_northeast_req_i        (tcdm_slave_northeast_req_i[t]               ),
      .tcdm_slave_northeast_req_valid_i  (tcdm_slave_northeast_req_valid_i[t]         ),
      .tcdm_slave_northeast_req_ready_o  (tcdm_slave_northeast_req_ready_o[t]         ),
      .tcdm_slave_northeast_resp_o       (tcdm_slave_northeast_resp[t]                ),
      .tcdm_slave_northeast_resp_valid_o (tcdm_slave_northeast_resp_valid[t]          ),
      .tcdm_slave_northeast_resp_ready_i (tcdm_slave_northeast_resp_ready[t]          ),
      .tcdm_slave_local_req_i            (tcdm_slave_local_req[t]                     ),
      .tcdm_slave_local_req_valid_i      (tcdm_slave_local_req_valid[t]               ),
      .tcdm_slave_local_req_ready_o      (tcdm_slave_local_req_ready[t]               ),
      .tcdm_slave_local_resp_o           (tcdm_slave_local_resp[t]                    ),
      .tcdm_slave_local_resp_valid_o     (tcdm_slave_local_resp_valid[t]              ),
      .tcdm_slave_local_resp_ready_i     (tcdm_slave_local_resp_ready[t]              ),
      // AXI interface
      .axi_mst_req_o                     (/* Not connected */                         ),
      .axi_mst_resp_i                    (/* Not connected */                         ),
      // Instruction refill interface
      .refill_qaddr_o                    (/* Not yet implemented */                   ),
      .refill_qlen_o                     (/* Not yet implemented */                   ), // AXI signal
      .refill_qvalid_o                   (/* Not yet implemented */                   ),
      .refill_qready_i                   (/* Not yet implemented */ '0                ),
      .refill_pdata_i                    (/* Not yet implemented */ '0                ),
      .refill_perror_i                   (/* Not yet implemented */ '0                ),
      .refill_pvalid_i                   (/* Not yet implemented */ '0                ),
      .refill_plast_i                    (/* Not yet implemented */ '0                ),
      .refill_pready_o                   (/* Not yet implemented */                   ),
      // Wake up interface
      .wake_up_i                         (wake_up_i[t*NumCoresPerTile +: NumCoresPerTile])
    );
  end : gen_tiles

  /*************************
   *  Local Interconnect  *
   *************************/

  logic           [NumTilesPerGroup-1:0] master_local_req_valid;
  logic           [NumTilesPerGroup-1:0] master_local_req_ready;
  tcdm_addr_t     [NumTilesPerGroup-1:0] master_local_req_tgt_addr;
  logic           [NumTilesPerGroup-1:0] master_local_req_wen;
  tcdm_payload_t  [NumTilesPerGroup-1:0] master_local_req_wdata;
  strb_t          [NumTilesPerGroup-1:0] master_local_req_be;
  logic           [NumTilesPerGroup-1:0] master_local_resp_valid;
  logic           [NumTilesPerGroup-1:0] master_local_resp_ready;
  tcdm_payload_t  [NumTilesPerGroup-1:0] master_local_resp_rdata;
  logic           [NumTilesPerGroup-1:0] slave_local_req_valid;
  logic           [NumTilesPerGroup-1:0] slave_local_req_ready;
  tile_addr_t     [NumTilesPerGroup-1:0] slave_local_req_tgt_addr;
  tile_group_id_t [NumTilesPerGroup-1:0] slave_local_req_ini_addr;
  logic           [NumTilesPerGroup-1:0] slave_local_req_wen;
  tcdm_payload_t  [NumTilesPerGroup-1:0] slave_local_req_wdata;
  strb_t          [NumTilesPerGroup-1:0] slave_local_req_be;
  logic           [NumTilesPerGroup-1:0] slave_local_resp_valid;
  logic           [NumTilesPerGroup-1:0] slave_local_resp_ready;
  tile_group_id_t [NumTilesPerGroup-1:0] slave_local_resp_ini_addr;
  tcdm_payload_t  [NumTilesPerGroup-1:0] slave_local_resp_rdata;

  for (genvar t = 0; t < NumTilesPerGroup; t++) begin: gen_local_connections
    assign master_local_req_valid[t]        = tcdm_master_local_req_valid[t];
    assign master_local_req_tgt_addr[t]     = tcdm_master_local_req[t].tgt_addr;
    assign master_local_req_wen[t]          = tcdm_master_local_req[t].wen;
    assign master_local_req_wdata[t]        = tcdm_master_local_req[t].wdata;
    assign master_local_req_be[t]           = tcdm_master_local_req[t].be;
    assign tcdm_master_local_req_ready[t]   = master_local_req_ready[t];
    assign slave_local_resp_valid[t]        = tcdm_slave_local_resp_valid[t];
    assign slave_local_resp_ini_addr[t]     = tcdm_slave_local_resp[t].ini_addr;
    assign slave_local_resp_rdata[t]        = tcdm_slave_local_resp[t].rdata;
    assign tcdm_slave_local_resp_ready[t]   = slave_local_resp_ready[t];
    assign tcdm_master_local_resp_valid[t]  = master_local_resp_valid[t];
    assign tcdm_master_local_resp[t].rdata  = master_local_resp_rdata[t];
    assign master_local_resp_ready[t]       = tcdm_master_local_resp_ready[t];
    assign tcdm_slave_local_req_valid[t]    = slave_local_req_valid[t];
    assign tcdm_slave_local_req[t].tgt_addr = slave_local_req_tgt_addr[t];
    assign tcdm_slave_local_req[t].ini_addr = slave_local_req_ini_addr[t];
    assign tcdm_slave_local_req[t].wen      = slave_local_req_wen[t];
    assign tcdm_slave_local_req[t].wdata    = slave_local_req_wdata[t];
    assign tcdm_slave_local_req[t].be       = slave_local_req_be[t];
    assign slave_local_req_ready[t]         = tcdm_slave_local_req_ready[t];
  end

  variable_latency_interconnect #(
    .NumIn       (NumTilesPerGroup                             ),
    .NumOut      (NumTilesPerGroup                             ),
    .AddrWidth   (TCDMAddrWidth                                ),
    .DataWidth   ($bits(tcdm_payload_t)                        ),
    .BeWidth     (DataWidth/8                                  ),
    .ByteOffWidth(0                                            ),
    .AddrMemWidth(TCDMAddrMemWidth + idx_width(NumBanksPerTile)),
    .Topology    (tcdm_interconnect_pkg::LIC                   ),
    .AxiVldRdy   (1'b1                                         )
  ) i_local_interco (
    .clk_i          (clk_i                    ),
    .rst_ni         (rst_ni                   ),
    .req_valid_i    (master_local_req_valid   ),
    .req_ready_o    (master_local_req_ready   ),
    .req_tgt_addr_i (master_local_req_tgt_addr),
    .req_wen_i      (master_local_req_wen     ),
    .req_wdata_i    (master_local_req_wdata   ),
    .req_be_i       (master_local_req_be      ),
    .resp_valid_o   (master_local_resp_valid  ),
    .resp_ready_i   (master_local_resp_ready  ),
    .resp_rdata_o   (master_local_resp_rdata  ),
    .resp_ini_addr_i(slave_local_resp_ini_addr),
    .resp_rdata_i   (slave_local_resp_rdata   ),
    .resp_valid_i   (slave_local_resp_valid   ),
    .resp_ready_o   (slave_local_resp_ready   ),
    .req_valid_o    (slave_local_req_valid    ),
    .req_ready_i    (slave_local_req_ready    ),
    .req_be_o       (slave_local_req_be       ),
    .req_wdata_o    (slave_local_req_wdata    ),
    .req_wen_o      (slave_local_req_wen      ),
    .req_ini_addr_o (slave_local_req_ini_addr ),
    .req_tgt_addr_o (slave_local_req_tgt_addr )
  );

  /***********************
   *  East Interconnect  *
   ***********************/

  logic           [NumTilesPerGroup-1:0] master_east_req_valid;
  logic           [NumTilesPerGroup-1:0] master_east_req_ready;
  tcdm_addr_t     [NumTilesPerGroup-1:0] master_east_req_tgt_addr;
  logic           [NumTilesPerGroup-1:0] master_east_req_wen;
  tcdm_payload_t  [NumTilesPerGroup-1:0] master_east_req_wdata;
  strb_t          [NumTilesPerGroup-1:0] master_east_req_be;
  logic           [NumTilesPerGroup-1:0] master_east_resp_valid;
  logic           [NumTilesPerGroup-1:0] master_east_resp_ready;
  tcdm_payload_t  [NumTilesPerGroup-1:0] master_east_resp_rdata;
  logic           [NumTilesPerGroup-1:0] slave_east_req_valid;
  logic           [NumTilesPerGroup-1:0] slave_east_req_ready;
  tile_addr_t     [NumTilesPerGroup-1:0] slave_east_req_tgt_addr;
  tile_group_id_t [NumTilesPerGroup-1:0] slave_east_req_ini_addr;
  logic           [NumTilesPerGroup-1:0] slave_east_req_wen;
  tcdm_payload_t  [NumTilesPerGroup-1:0] slave_east_req_wdata;
  strb_t          [NumTilesPerGroup-1:0] slave_east_req_be;
  logic           [NumTilesPerGroup-1:0] slave_east_resp_valid;
  logic           [NumTilesPerGroup-1:0] slave_east_resp_ready;
  tile_group_id_t [NumTilesPerGroup-1:0] slave_east_resp_ini_addr;
  tcdm_payload_t  [NumTilesPerGroup-1:0] slave_east_resp_rdata;

  for (genvar t = 0; t < NumTilesPerGroup; t++) begin: gen_east_connections
    assign master_east_req_valid[t]           = tcdm_master_east_req_valid[t];
    assign master_east_req_tgt_addr[t]        = tcdm_master_east_req[t].tgt_addr;
    assign master_east_req_wen[t]             = tcdm_master_east_req[t].wen;
    assign master_east_req_wdata[t]           = tcdm_master_east_req[t].wdata;
    assign master_east_req_be[t]              = tcdm_master_east_req[t].be;
    assign tcdm_master_east_req_ready[t]      = master_east_req_ready[t];
    assign tcdm_master_east_req_valid_o[t]    = slave_east_req_valid[t];
    assign tcdm_master_east_req_o[t].tgt_addr = slave_east_req_tgt_addr[t];
    assign tcdm_master_east_req_o[t].ini_addr = slave_east_req_ini_addr[t];
    assign tcdm_master_east_req_o[t].wen      = slave_east_req_wen[t];
    assign tcdm_master_east_req_o[t].wdata    = slave_east_req_wdata[t];
    assign tcdm_master_east_req_o[t].be       = slave_east_req_be[t];
    assign slave_east_req_ready[t]            = tcdm_master_east_req_ready_i[t];
    assign slave_east_resp_valid[t]           = tcdm_slave_east_resp_valid[t];
    assign slave_east_resp_ini_addr[t]        = tcdm_slave_east_resp[t].ini_addr;
    assign slave_east_resp_rdata[t]           = tcdm_slave_east_resp[t].rdata;
    assign tcdm_slave_east_resp_ready[t]      = slave_east_resp_ready[t];
    assign tcdm_slave_east_resp_valid_o[t]    = master_east_resp_valid[t];
    assign tcdm_slave_east_resp_o[t].rdata    = master_east_resp_rdata[t];
    assign master_east_resp_ready[t]          = tcdm_slave_east_resp_ready_i[t];
  end

  variable_latency_interconnect #(
    .NumIn              (NumTilesPerGroup                             ),
    .NumOut             (NumTilesPerGroup                             ),
    .AddrWidth          (TCDMAddrWidth                                ),
    .DataWidth          ($bits(tcdm_payload_t)                        ),
    .BeWidth            (DataWidth/8                                  ),
    .ByteOffWidth       (0                                            ),
    .AddrMemWidth       (TCDMAddrMemWidth + idx_width(NumBanksPerTile)),
    .Topology           (tcdm_interconnect_pkg::BFLY4                 ),
    .AxiVldRdy          (1'b1                                         ),
    .SpillRegisterReq   (64'b10                                       ),
    .SpillRegisterResp  (64'b10                                       ),
    .FallThroughRegister(1'b1                                         )
  ) i_east_interco (
    .clk_i          (clk_i                   ),
    .rst_ni         (rst_ni                  ),
    .req_valid_i    (master_east_req_valid   ),
    .req_ready_o    (master_east_req_ready   ),
    .req_tgt_addr_i (master_east_req_tgt_addr),
    .req_wen_i      (master_east_req_wen     ),
    .req_wdata_i    (master_east_req_wdata   ),
    .req_be_i       (master_east_req_be      ),
    .resp_valid_o   (master_east_resp_valid  ),
    .resp_ready_i   (master_east_resp_ready  ),
    .resp_rdata_o   (master_east_resp_rdata  ),
    .resp_ini_addr_i(slave_east_resp_ini_addr),
    .resp_rdata_i   (slave_east_resp_rdata   ),
    .resp_valid_i   (slave_east_resp_valid   ),
    .resp_ready_o   (slave_east_resp_ready   ),
    .req_valid_o    (slave_east_req_valid    ),
    .req_ready_i    (slave_east_req_ready    ),
    .req_be_o       (slave_east_req_be       ),
    .req_wdata_o    (slave_east_req_wdata    ),
    .req_wen_o      (slave_east_req_wen      ),
    .req_ini_addr_o (slave_east_req_ini_addr ),
    .req_tgt_addr_o (slave_east_req_tgt_addr )
  );

  /************************
   *  North Interconnect  *
   ************************/

  logic           [NumTilesPerGroup-1:0] master_north_req_valid;
  logic           [NumTilesPerGroup-1:0] master_north_req_ready;
  tcdm_addr_t     [NumTilesPerGroup-1:0] master_north_req_tgt_addr;
  logic           [NumTilesPerGroup-1:0] master_north_req_wen;
  tcdm_payload_t  [NumTilesPerGroup-1:0] master_north_req_wdata;
  strb_t          [NumTilesPerGroup-1:0] master_north_req_be;
  logic           [NumTilesPerGroup-1:0] master_north_resp_valid;
  logic           [NumTilesPerGroup-1:0] master_north_resp_ready;
  tcdm_payload_t  [NumTilesPerGroup-1:0] master_north_resp_rdata;
  logic           [NumTilesPerGroup-1:0] slave_north_req_valid;
  logic           [NumTilesPerGroup-1:0] slave_north_req_ready;
  tile_addr_t     [NumTilesPerGroup-1:0] slave_north_req_tgt_addr;
  tile_group_id_t [NumTilesPerGroup-1:0] slave_north_req_ini_addr;
  logic           [NumTilesPerGroup-1:0] slave_north_req_wen;
  tcdm_payload_t  [NumTilesPerGroup-1:0] slave_north_req_wdata;
  strb_t          [NumTilesPerGroup-1:0] slave_north_req_be;
  logic           [NumTilesPerGroup-1:0] slave_north_resp_valid;
  logic           [NumTilesPerGroup-1:0] slave_north_resp_ready;
  tile_group_id_t [NumTilesPerGroup-1:0] slave_north_resp_ini_addr;
  tcdm_payload_t  [NumTilesPerGroup-1:0] slave_north_resp_rdata;

  for (genvar t = 0; t < NumTilesPerGroup; t++) begin: gen_north_connections
    assign master_north_req_valid[t]           = tcdm_master_north_req_valid[t];
    assign master_north_req_tgt_addr[t]        = tcdm_master_north_req[t].tgt_addr;
    assign master_north_req_wen[t]             = tcdm_master_north_req[t].wen;
    assign master_north_req_wdata[t]           = tcdm_master_north_req[t].wdata;
    assign master_north_req_be[t]              = tcdm_master_north_req[t].be;
    assign tcdm_master_north_req_ready[t]      = master_north_req_ready[t];
    assign tcdm_master_north_req_valid_o[t]    = slave_north_req_valid[t];
    assign tcdm_master_north_req_o[t].tgt_addr = slave_north_req_tgt_addr[t];
    assign tcdm_master_north_req_o[t].ini_addr = slave_north_req_ini_addr[t];
    assign tcdm_master_north_req_o[t].wen      = slave_north_req_wen[t];
    assign tcdm_master_north_req_o[t].wdata    = slave_north_req_wdata[t];
    assign tcdm_master_north_req_o[t].be       = slave_north_req_be[t];
    assign slave_north_req_ready[t]            = tcdm_master_north_req_ready_i[t];
    assign slave_north_resp_valid[t]           = tcdm_slave_north_resp_valid[t];
    assign slave_north_resp_ini_addr[t]        = tcdm_slave_north_resp[t].ini_addr;
    assign slave_north_resp_rdata[t]           = tcdm_slave_north_resp[t].rdata;
    assign tcdm_slave_north_resp_ready[t]      = slave_north_resp_ready[t];
    assign tcdm_slave_north_resp_valid_o[t]    = master_north_resp_valid[t];
    assign tcdm_slave_north_resp_o[t].rdata    = master_north_resp_rdata[t];
    assign master_north_resp_ready[t]          = tcdm_slave_north_resp_ready_i[t];
  end

  variable_latency_interconnect #(
    .NumIn              (NumTilesPerGroup                             ),
    .NumOut             (NumTilesPerGroup                             ),
    .AddrWidth          (TCDMAddrWidth                                ),
    .DataWidth          ($bits(tcdm_payload_t)                        ),
    .BeWidth            (DataWidth/8                                  ),
    .ByteOffWidth       (0                                            ),
    .AddrMemWidth       (TCDMAddrMemWidth + idx_width(NumBanksPerTile)),
    .Topology           (tcdm_interconnect_pkg::BFLY4                 ),
    .AxiVldRdy          (1'b1                                         ),
    .SpillRegisterReq   (64'b10                                       ),
    .SpillRegisterResp  (64'b10                                       ),
    .FallThroughRegister(1'b1                                         )
  ) i_north_interco (
    .clk_i          (clk_i                    ),
    .rst_ni         (rst_ni                   ),
    .req_valid_i    (master_north_req_valid   ),
    .req_ready_o    (master_north_req_ready   ),
    .req_tgt_addr_i (master_north_req_tgt_addr),
    .req_wen_i      (master_north_req_wen     ),
    .req_wdata_i    (master_north_req_wdata   ),
    .req_be_i       (master_north_req_be      ),
    .resp_valid_o   (master_north_resp_valid  ),
    .resp_ready_i   (master_north_resp_ready  ),
    .resp_rdata_o   (master_north_resp_rdata  ),
    .req_valid_o    (slave_north_req_valid    ),
    .req_ready_i    (slave_north_req_ready    ),
    .req_be_o       (slave_north_req_be       ),
    .req_wdata_o    (slave_north_req_wdata    ),
    .req_wen_o      (slave_north_req_wen      ),
    .req_ini_addr_o (slave_north_req_ini_addr ),
    .req_tgt_addr_o (slave_north_req_tgt_addr ),
    .resp_ini_addr_i(slave_north_resp_ini_addr),
    .resp_rdata_i   (slave_north_resp_rdata   ),
    .resp_valid_i   (slave_north_resp_valid   ),
    .resp_ready_o   (slave_north_resp_ready   )
  );

  /****************************
   *  Northeast Interconnect  *
   ****************************/

  logic           [NumTilesPerGroup-1:0] master_northeast_req_valid;
  logic           [NumTilesPerGroup-1:0] master_northeast_req_ready;
  tcdm_addr_t     [NumTilesPerGroup-1:0] master_northeast_req_tgt_addr;
  logic           [NumTilesPerGroup-1:0] master_northeast_req_wen;
  tcdm_payload_t  [NumTilesPerGroup-1:0] master_northeast_req_wdata;
  strb_t          [NumTilesPerGroup-1:0] master_northeast_req_be;
  logic           [NumTilesPerGroup-1:0] master_northeast_resp_valid;
  logic           [NumTilesPerGroup-1:0] master_northeast_resp_ready;
  tcdm_payload_t  [NumTilesPerGroup-1:0] master_northeast_resp_rdata;
  logic           [NumTilesPerGroup-1:0] slave_northeast_req_valid;
  logic           [NumTilesPerGroup-1:0] slave_northeast_req_ready;
  tile_addr_t     [NumTilesPerGroup-1:0] slave_northeast_req_tgt_addr;
  tile_group_id_t [NumTilesPerGroup-1:0] slave_northeast_req_ini_addr;
  logic           [NumTilesPerGroup-1:0] slave_northeast_req_wen;
  tcdm_payload_t  [NumTilesPerGroup-1:0] slave_northeast_req_wdata;
  strb_t          [NumTilesPerGroup-1:0] slave_northeast_req_be;
  logic           [NumTilesPerGroup-1:0] slave_northeast_resp_valid;
  logic           [NumTilesPerGroup-1:0] slave_northeast_resp_ready;
  tile_group_id_t [NumTilesPerGroup-1:0] slave_northeast_resp_ini_addr;
  tcdm_payload_t  [NumTilesPerGroup-1:0] slave_northeast_resp_rdata;

  for (genvar t = 0; t < NumTilesPerGroup; t++) begin: gen_northeast_connections
    assign master_northeast_req_valid[t]           = tcdm_master_northeast_req_valid[t];
    assign master_northeast_req_tgt_addr[t]        = tcdm_master_northeast_req[t].tgt_addr;
    assign master_northeast_req_wen[t]             = tcdm_master_northeast_req[t].wen;
    assign master_northeast_req_wdata[t]           = tcdm_master_northeast_req[t].wdata;
    assign master_northeast_req_be[t]              = tcdm_master_northeast_req[t].be;
    assign tcdm_master_northeast_req_ready[t]      = master_northeast_req_ready[t];
    assign tcdm_master_northeast_req_valid_o[t]    = slave_northeast_req_valid[t];
    assign tcdm_master_northeast_req_o[t].tgt_addr = slave_northeast_req_tgt_addr[t];
    assign tcdm_master_northeast_req_o[t].ini_addr = slave_northeast_req_ini_addr[t];
    assign tcdm_master_northeast_req_o[t].wen      = slave_northeast_req_wen[t];
    assign tcdm_master_northeast_req_o[t].wdata    = slave_northeast_req_wdata[t];
    assign tcdm_master_northeast_req_o[t].be       = slave_northeast_req_be[t];
    assign slave_northeast_req_ready[t]            = tcdm_master_northeast_req_ready_i[t];
    assign slave_northeast_resp_valid[t]           = tcdm_slave_northeast_resp_valid[t];
    assign slave_northeast_resp_ini_addr[t]        = tcdm_slave_northeast_resp[t].ini_addr;
    assign slave_northeast_resp_rdata[t]           = tcdm_slave_northeast_resp[t].rdata;
    assign tcdm_slave_northeast_resp_ready[t]      = slave_northeast_resp_ready[t];
    assign tcdm_slave_northeast_resp_valid_o[t]    = master_northeast_resp_valid[t];
    assign tcdm_slave_northeast_resp_o[t].rdata    = master_northeast_resp_rdata[t];
    assign master_northeast_resp_ready[t]          = tcdm_slave_northeast_resp_ready_i[t];
  end

  variable_latency_interconnect #(
    .NumIn              (NumTilesPerGroup                             ),
    .NumOut             (NumTilesPerGroup                             ),
    .AddrWidth          (TCDMAddrWidth                                ),
    .DataWidth          ($bits(tcdm_payload_t)                        ),
    .BeWidth            (DataWidth/8                                  ),
    .ByteOffWidth       (0                                            ),
    .AddrMemWidth       (TCDMAddrMemWidth + idx_width(NumBanksPerTile)),
    .Topology           (tcdm_interconnect_pkg::BFLY4                 ),
    .AxiVldRdy          (1'b1                                         ),
    .SpillRegisterReq   (64'b10                                       ),
    .SpillRegisterResp  (64'b10                                       ),
    .FallThroughRegister(1'b1                                         )
  ) i_northeast_interco (
    .clk_i          (clk_i                        ),
    .rst_ni         (rst_ni                       ),
    .req_valid_i    (master_northeast_req_valid   ),
    .req_ready_o    (master_northeast_req_ready   ),
    .req_tgt_addr_i (master_northeast_req_tgt_addr),
    .req_wen_i      (master_northeast_req_wen     ),
    .req_wdata_i    (master_northeast_req_wdata   ),
    .req_be_i       (master_northeast_req_be      ),
    .resp_valid_o   (master_northeast_resp_valid  ),
    .resp_ready_i   (master_northeast_resp_ready  ),
    .resp_rdata_o   (master_northeast_resp_rdata  ),
    .resp_ini_addr_i(slave_northeast_resp_ini_addr),
    .resp_rdata_i   (slave_northeast_resp_rdata   ),
    .resp_valid_i   (slave_northeast_resp_valid   ),
    .resp_ready_o   (slave_northeast_resp_ready   ),
    .req_valid_o    (slave_northeast_req_valid    ),
    .req_ready_i    (slave_northeast_req_ready    ),
    .req_be_o       (slave_northeast_req_be       ),
    .req_wdata_o    (slave_northeast_req_wdata    ),
    .req_wen_o      (slave_northeast_req_wen      ),
    .req_ini_addr_o (slave_northeast_req_ini_addr ),
    .req_tgt_addr_o (slave_northeast_req_tgt_addr )
  );

endmodule: mempool_group
