// Copyright 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

package mempool_pkg;

  import snitch_pkg::ReorderIdWidth;
  import cf_math_pkg::idx_width;

  /***********************
   *  MEMORY PARAMETERS  *
   ***********************/

  localparam integer unsigned AddrWidth        = 32;
  localparam integer unsigned DataWidth        = 32;
  localparam integer unsigned BeWidth          = DataWidth / 8;
  localparam integer unsigned ByteOffset       = $clog2(BeWidth);
  localparam integer unsigned TCDMSizePerBank  = 1024 /* [B] */;
  localparam integer unsigned TCDMAddrMemWidth = $clog2(TCDMSizePerBank / mempool_pkg::BeWidth);

  /*********************
   *  TILE PARAMETERS  *
   *********************/

  `include "axi/assign.svh"
  `include "axi/typedef.svh"

  localparam integer unsigned NumCoresPerTile  = `ifdef NUM_CORES_PER_TILE `NUM_CORES_PER_TILE `else 0 `endif;
  localparam integer unsigned NumCores         = `ifdef NUM_CORES `NUM_CORES `else 0 `endif;
  localparam integer unsigned NumTiles         = NumCores / NumCoresPerTile;
  localparam integer unsigned NumCoresPerCache = NumCoresPerTile;
  localparam integer unsigned NumGroups        = 4;
  localparam integer unsigned AxiCoreIdWidth   = $clog2(NumCoresPerTile);
  localparam integer unsigned AxiTileIdWidth   = AxiCoreIdWidth+1; // + 1 for cache

  typedef logic [AxiCoreIdWidth-1:0] axi_core_id_t;
  typedef logic [AxiTileIdWidth-1:0] axi_tile_id_t;
  typedef logic [AddrWidth-1:0] addr_t;
  typedef logic [DataWidth-1:0] data_t;
  typedef logic [BeWidth-1:0] strb_t;

  localparam NumSystemXbarMasters = NumTiles + 1;
  localparam AxiSystemIdWidth = $clog2(NumSystemXbarMasters) + AxiTileIdWidth;
  typedef logic [AxiSystemIdWidth-1:0] axi_system_id_t;

  localparam NumTestbenchXbarMasters = 1;
  localparam AxiTestbenchIdWidth = $clog2(NumTestbenchXbarMasters) + AxiSystemIdWidth;
  typedef logic [AxiTestbenchIdWidth-1:0] axi_tb_id_t;


  `AXI_TYPEDEF_AW_CHAN_T(axi_core_aw_t, addr_t, axi_core_id_t, logic);
  `AXI_TYPEDEF_W_CHAN_T(axi_core_w_t, data_t, strb_t, logic);
  `AXI_TYPEDEF_B_CHAN_T(axi_core_b_t, axi_core_id_t, logic);
  `AXI_TYPEDEF_AR_CHAN_T(axi_core_ar_t, addr_t, axi_core_id_t, logic);
  `AXI_TYPEDEF_R_CHAN_T(axi_core_r_t, data_t, axi_core_id_t, logic);
  `AXI_TYPEDEF_REQ_T(axi_core_req_t, axi_core_aw_t, axi_core_w_t, axi_core_ar_t);
  `AXI_TYPEDEF_RESP_T(axi_core_resp_t, axi_core_b_t, axi_core_r_t );

  `AXI_TYPEDEF_AW_CHAN_T(axi_tile_aw_t, addr_t, axi_tile_id_t, logic);
  `AXI_TYPEDEF_W_CHAN_T(axi_tile_w_t, data_t, strb_t, logic);
  `AXI_TYPEDEF_B_CHAN_T(axi_tile_b_t, axi_tile_id_t, logic);
  `AXI_TYPEDEF_AR_CHAN_T(axi_tile_ar_t, addr_t, axi_tile_id_t, logic);
  `AXI_TYPEDEF_R_CHAN_T(axi_tile_r_t, data_t, axi_tile_id_t, logic);
  `AXI_TYPEDEF_REQ_T(axi_tile_req_t, axi_tile_aw_t, axi_tile_w_t, axi_tile_ar_t);
  `AXI_TYPEDEF_RESP_T(axi_tile_resp_t, axi_tile_b_t, axi_tile_r_t );

  `AXI_TYPEDEF_AW_CHAN_T(axi_system_aw_t, addr_t, axi_system_id_t, logic);
  `AXI_TYPEDEF_W_CHAN_T(axi_system_w_t, data_t, strb_t, logic);
  `AXI_TYPEDEF_B_CHAN_T(axi_system_b_t, axi_system_id_t, logic);
  `AXI_TYPEDEF_AR_CHAN_T(axi_system_ar_t, addr_t, axi_system_id_t, logic);
  `AXI_TYPEDEF_R_CHAN_T(axi_system_r_t, data_t, axi_system_id_t, logic);
  `AXI_TYPEDEF_REQ_T(axi_system_req_t, axi_system_aw_t, axi_system_w_t, axi_system_ar_t);
  `AXI_TYPEDEF_RESP_T(axi_system_resp_t, axi_system_b_t, axi_system_r_t);

  `AXI_TYPEDEF_AW_CHAN_T(axi_tb_aw_t, addr_t, axi_tb_id_t, logic);
  `AXI_TYPEDEF_W_CHAN_T(axi_tb_w_t, data_t, strb_t, logic);
  `AXI_TYPEDEF_B_CHAN_T(axi_tb_b_t, axi_tb_id_t, logic);
  `AXI_TYPEDEF_AR_CHAN_T(axi_tb_ar_t, addr_t, axi_tb_id_t, logic);
  `AXI_TYPEDEF_R_CHAN_T(axi_tb_r_t, data_t, axi_tb_id_t, logic);
  `AXI_TYPEDEF_REQ_T(axi_tb_req_t, axi_tb_aw_t, axi_tb_w_t, axi_tb_ar_t);
  `AXI_TYPEDEF_RESP_T(axi_tb_resp_t, axi_tb_b_t, axi_tb_r_t);

  `AXI_LITE_TYPEDEF_AW_CHAN_T(axi_lite_slv_aw_t, addr_t)
  `AXI_LITE_TYPEDEF_W_CHAN_T(axi_lite_slv_w_t, data_t, strb_t)
  `AXI_LITE_TYPEDEF_B_CHAN_T(axi_lite_slv_b_t)
  `AXI_LITE_TYPEDEF_AR_CHAN_T(axi_lite_slv_ar_t, addr_t)
  `AXI_LITE_TYPEDEF_R_CHAN_T(axi_lite_slv_r_t, data_t)
  `AXI_LITE_TYPEDEF_REQ_T(axi_lite_slv_req_t, axi_lite_slv_aw_t, axi_lite_slv_w_t, axi_lite_slv_ar_t)
  `AXI_LITE_TYPEDEF_RESP_T(axi_lite_slv_resp_t, axi_lite_slv_b_t, axi_lite_slv_r_t)

  /***********************
   *  INSTRUCTION CACHE  *
   ***********************/

  localparam int unsigned ICacheSizeByte  = 512 * NumCoresPerCache; // Total Size of instruction cache in bytes
  localparam int unsigned ICacheSets      = NumCoresPerCache;       // Number of sets
  localparam int unsigned ICacheLineWidth = 32 * NumCoresPerCache;  // Size of each cache line in bits,

  /**********************************
   *  TCDM INTERCONNECT PARAMETERS  *
   **********************************/

  typedef logic [TCDMAddrMemWidth-1:0] bank_addr_t;
  typedef logic [ReorderIdWidth-1:0] reorder_id_t;
  typedef logic [idx_width(NumCoresPerTile)-1:0] tile_core_id_t;
  typedef logic [idx_width(NumGroups)-1:0] group_id_t;
  typedef logic [3:0] amo_t;

  typedef struct packed {
    reorder_id_t reorder_id;
    tile_core_id_t core_id;
    amo_t amo;
    data_t data;
  } tcdm_payload_t;

  /*****************
   *  ADDRESS MAP  *
   *****************/

  // Size in bytes of memory that is sequentially addressable per tile
  localparam int unsigned SeqMemSizePerTile = NumCoresPerTile*1024; // 1 KiB

  typedef struct packed {
    int unsigned slave_idx;
    addr_t mask;
    addr_t value;
  } address_map_t;

endpackage : mempool_pkg
