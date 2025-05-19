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

  // Memory read requests are bursted
  localparam bit UseBurst = `ifdef TCDM_BURST `TCDM_BURST `else 0 `endif;

  // Maximum length of the issued burst
  localparam integer unsigned BurstLen = `ifdef TCDM_BURSTLEN `TCDM_BURSTLEN `else 1 `endif;
  parameter int unsigned BurstLenWidth = BurstLen == 1 ? 1 : $clog2(BurstLen);

  // Number of cuts if a burst crosses the target memory boundary
  localparam integer unsigned NumCuts = 1;

  typedef struct packed {
    logic isburst;
    logic [BurstLenWidth-1:0] blen;
  } burst_t;

  /*********************************
   *  TCDM Grouped Rsp PARAMETERS  *
   *********************************/

 // Grouping Factor of response data
  localparam integer unsigned RspGF = `ifdef GROUP_RSP `GROUP_RSP `else 1 `endif;

  // replace rdata payload with this when the response is grouped
  localparam int RspBurstMSB = (RspGF > 1) ? (RspGF - 2) : 0;
  typedef logic [RspBurstMSB:0][31:0] burst_gresp_t;

endpackage : tcdm_burst_pkg
