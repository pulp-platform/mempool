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
  localparam bit UseBurst = `ifdef TCDM_BURST `TCDM_BURST `else 0 `endif;

  // Maximum length of burst
  localparam int MaxBurstLen   = UseBurst ? 2 : 1;

  // 0 to MaxBurstLen
  localparam int BurstLenWidth = $clog2(MaxBurstLen);

  typedef struct packed {
    logic burst;
    logic [BurstLenWidth:0] blen;
  } tcdm_breq_t;

  /*********************************
   *  TCDM Grouped Rsp PARAMETERS  *
   *********************************/

	// Grouped Response Extension
  localparam bit GroupRsp = `ifdef GROUP_RSP `GROUP_RSP `else 0 `endif;

  // Parallel Burst Manager
  localparam bit ParallelManager = (GroupRsp > 1) ? `PARALLEL_MANAGER : 0;

  // Grouping Factor of response data
  localparam integer unsigned RspGF = GroupRsp ? 2 : 1;

  `ifdef GROUP_RSP
  	typedef struct packed {
      logic  [RspGF-2:0][31:0] data;
      logic  valid;
    } tcdm_gre_t;
  `else
    // still define the type but mimize the wire if not used
    typedef struct packed {
      logic data;
      logic valid;
    } tcdm_gre_t;
  `endif
endpackage : tcdm_burst_pkg
