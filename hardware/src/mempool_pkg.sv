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

  /***********************
   *  MEMORY PARAMETERS  *
   ***********************/

  localparam AddrWidth  = 32             ;
  localparam DataWidth  = 32             ;
  localparam BeWidth    = DataWidth / 8  ;
  localparam ByteOffset = $clog2(BeWidth);

  /**********************************
   *  TCDM INTERCONNECT PARAMETERS  *
   **********************************/

  typedef logic [AddrWidth-1:0] addr_t           ;
  typedef logic [DataWidth-1:0] data_t           ;
  typedef logic [ReorderIdWidth-1:0] reorder_id_t;
  typedef logic [BeWidth-1:0] strb_t             ;
  typedef logic [3:0] amo_t                      ;
  typedef struct packed {
    reorder_id_t id;
    amo_t amo      ;
    data_t data    ;
  } tcdm_payload_t;

  /*****************
   *  ADDRESS MAP  *
   *****************/

  typedef struct packed {
    int unsigned slave_idx;
    addr_t mask           ;
    addr_t value          ;
  } address_map_t;

endpackage : mempool_pkg
