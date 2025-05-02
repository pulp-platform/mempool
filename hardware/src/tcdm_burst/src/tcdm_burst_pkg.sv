// Copyright 2024 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Author: Diyou Shen, ETH Zurich
// Author: Marco Bertuletti ETH Zurich

// Description
// Include TCDM burst types and grouped response types

package tcdm_burst_pkg;
  /***************************
   *  TCDM BURST PARAMETERS  *
   ***************************/
  localparam bit UseBurst = `ifdef TCDM_BURST `TCDM_BURST `else 0 `endif;
  localparam integer unsigned BurstLen = `ifdef TCDM_BURSTLEN `TCDM_BURSTLEN `else 1 `endif;
  localparam integer unsigned NumCuts = 1;

  // Maximum length of burst
  parameter int unsigned MaxBurstLen   = UseBurst ? BurstLen : 1;
  // 0 to MaxBurstLen
  parameter int unsigned MaxBurstLenWidth = $clog2(MaxBurstLen);

  typedef struct packed {
    logic isburst;
    logic [MaxBurstLenWidth-1:0] blen;
  } burst_t;

  /*********************************
   *  TCDM Grouped Rsp PARAMETERS  *
   *********************************/

  // Grouped Response Extension
  localparam bit GroupRsp = `ifdef GROUP_RSP `GROUP_RSP `else 0 `endif;

  // Grouping Factor of response data
  localparam integer unsigned RspGF = GroupRsp ? 2 : 1;

  // replace rdata payload with this when the response is grouped
  typedef struct packed {
    logic  [RspGF-1:0][31:0] data;
    logic  [RspGF-1:0] we;
  } burst_gresp_t;

endpackage : tcdm_burst_pkg
