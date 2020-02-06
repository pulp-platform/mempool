// Copyright 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

`include "axi/typedef.svh"

package mempool_pkg;

  /*************
   *  MEMPOOL  *
   *************/

  localparam NumCores        = 32                             ;
  localparam NumCoresPerTile = 4                              ;
  localparam BankingFactor   = 4                              ;
  localparam NumBanksPerTile = NumCoresPerTile * BankingFactor;
  localparam NumTiles        = NumCores / NumCoresPerTile     ;
  localparam NumBanks        = NumBanksPerTile * NumTiles     ;

  /***********************
   *  MEMORY PARAMETERS  *
   ***********************/

  localparam AddrWidth  = 32             ;
  localparam DataWidth  = 32             ;
  localparam BeWidth    = DataWidth / 8  ;
  localparam ByteOffset = $clog2(BeWidth);

  localparam TCDMSizePerBank  = 1024                             ; // [B]
  localparam TCDMAddrMemWidth = $clog2(TCDMSizePerBank / BeWidth);

  /**********************************
   *  TCDM INTERCONNECT PARAMETERS  *
   **********************************/

  typedef logic [AddrWidth-1:0] addr_t                                    ;
  typedef logic [DataWidth-1:0] data_t                                    ;
  typedef logic [BeWidth-1:0] be_t                                        ;
  typedef logic [3:0] amo_t                                               ;
  typedef logic [$clog2(NumCores)-1:0] core_addr_t                        ;
  typedef logic [TCDMAddrMemWidth-1:0] tcdm_addr_t                        ;
  typedef logic [TCDMAddrMemWidth+$clog2(NumBanksPerTile)-1:0] tile_addr_t;

  localparam addr_t TCDMSize     = NumBanks * TCDMSizePerBank;
  localparam addr_t TCDMMask     = ~(TCDMSize - 1)           ;
  localparam addr_t TCDMBaseAddr = '0                        ;
  localparam addr_t TCDMEndAddr  = TCDMBaseAddr + TCDMSize   ;

  /*********************************
   *  AXI INTERCONNECT PARAMETERS  *
   *********************************/

  parameter int unsigned NumAXIMasters = NumTiles               ;
  parameter int unsigned AxiMstIdWidth = $clog2(NumCoresPerTile);
  parameter int unsigned AxiSlvIdWidth = $clog2(NumCores)       ;

  typedef addr_t axi_addr_t                     ;
  typedef logic axi_user_t                      ;
  typedef data_t axi_data_t                     ;
  typedef be_t axi_strb_t                       ;
  typedef logic [AxiMstIdWidth-1:0] axi_mst_id_t;
  typedef logic [AxiSlvIdWidth-1:0] axi_slv_id_t;

  // AXI types
  `AXI_TYPEDEF_AW_CHAN_T(axi_aw_t, axi_addr_t, axi_mst_id_t, axi_user_t);
  `AXI_TYPEDEF_W_CHAN_T(axi_w_t, axi_data_t, axi_strb_t, axi_user_t)    ;
  `AXI_TYPEDEF_B_CHAN_T(axi_b_t, axi_mst_id_t, axi_user_t)              ;
  `AXI_TYPEDEF_AR_CHAN_T(axi_ar_t, axi_addr_t, axi_mst_id_t, axi_user_t);
  `AXI_TYPEDEF_R_CHAN_T(axi_r_t, axi_data_t, axi_mst_id_t, axi_user_t)  ;
  `AXI_TYPEDEF_REQ_T(axi_req_t, axi_aw_t, axi_w_t, axi_ar_t)            ;
  `AXI_TYPEDEF_RESP_T(axi_resp_t, axi_b_t, axi_r_t )                    ;

  `AXI_TYPEDEF_AW_CHAN_T(axi_slv_aw_t, axi_addr_t, axi_slv_id_t, axi_user_t);
  `AXI_TYPEDEF_B_CHAN_T(axi_slv_b_t, axi_slv_id_t, axi_user_t)              ;
  `AXI_TYPEDEF_AR_CHAN_T(axi_slv_ar_t, axi_addr_t, axi_slv_id_t, axi_user_t);
  `AXI_TYPEDEF_R_CHAN_T(axi_slv_r_t, axi_data_t, axi_slv_id_t, axi_user_t)  ;
  `AXI_TYPEDEF_REQ_T(axi_slv_req_t, axi_slv_aw_t, axi_w_t, axi_slv_ar_t)    ;
  `AXI_TYPEDEF_RESP_T(axi_slv_resp_t, axi_slv_b_t, axi_slv_r_t)             ;

  /*****************
   *  ADDRESS MAP  *
   *****************/

  typedef struct packed {
    int unsigned slave_idx;
    addr_t mask           ;
    addr_t value          ;
  } address_map_t;

endpackage : mempool_pkg
