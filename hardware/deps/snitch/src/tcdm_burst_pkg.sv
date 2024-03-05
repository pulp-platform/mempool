// Copyright 2024 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Author: Diyou Shen, ETH Zurich

// Description
// Include TCDM burst types and grouped response types

package tcdm_burst_pkg;
	/***************************
   *  TCDM BURST PARAMETERS  *
   ***************************/
  localparam bit UseBurst = `ifdef TCDM_BLEN 1 `else 0 `endif;
  // localparam bit UseBurst 	   = 1;
  localparam int MaxBurstLen   = `ifdef TCDM_BLEN `TCDM_BLEN `else 1 `endif;
  // 0 to MaxBurstLen
  localparam int BurstLenWidth = UseBurst ? $clog2(MaxBurstLen)+1 : 1;

  typedef struct packed {
    logic burst;
    logic [BurstLenWidth-1:0] blen;
  } tcdm_breq_t;

  /*********************************
   *  TCDM Grouped Rsp PARAMETERS  *
   *********************************/

	// Grouped Response Extension
  localparam integer unsigned RspGF = `ifdef RSP_GF `RSP_GF `else 1 `endif;
	typedef struct packed {
`ifdef RSP_GF
    logic  [RspGF-2:0][31:0] data;
    logic  valid;
`else
    // still define the type but mimize the wire if not used
    logic data;
    logic valid;
`endif
  } tcdm_gre_t;

  // localparam integer unsigned RspGF = 8;

  // typedef struct packed {
  //   logic  [RspGF-2:0][31:0] data;
  //   logic  valid;
  // } tcdm_gre_t;


endpackage : tcdm_burst_pkg
