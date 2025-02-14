// Copyright 2021 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "mempool/mempool.svh"

module mempool_tile_id_remapper
  import mempool_pkg::*;
  import cf_math_pkg::idx_width;
#(
) (
  input  logic                                            clk_i,
  input  logic                                            rst_ni,

  input  group_id_t                                       group_id_i,

  input  tcdm_dma_req_t                                   tcdm_dma_req_i,
  input  tcdm_slave_req_t     [NumRemoteReqPortsPerTile-1:0] tcdm_slave_req_i,
  input  tcdm_slave_req_t     [NumCoresPerTile-1:0]       local_req_interco_payload_i,

  input  logic                [NumCoresPerTile-1:0]       remote_req_interco_valid_i,
  input  logic                [NumCoresPerTile-1:0]       remote_req_interco_ready_i,
  input  logic                [NumCoresPerTile-1:0]       remote_req_interco_wen_i,
  input  logic                [NumCoresPerTile-1:0]       remote_req_interco_amoen_i,
  // input  logic                [NumCoresPerTile-1:0][idx_width(NumRemoteReqPortsPerTile)-1:0]       remote_req_interco_tgt_sel_i,

  input  addr_t               [NumCoresPerTile-1:0]       prescramble_tcdm_req_tgt_addr_i,

  output tcdm_dma_req_t                                   tcdm_dma_req_remapped_o,
  output tcdm_slave_req_t     [NumRemoteReqPortsPerTile-1:0] tcdm_slave_req_remapped_o,
  output tcdm_slave_req_t     [NumCoresPerTile-1:0]       local_req_interco_payload_remapped_o,

  output logic                [NumCoresPerTile-1:0]       remote_req_interco_to_xbar_valid_o,
  output logic                [NumCoresPerTile-1:0]       remote_req_interco_to_xbar_ready_o,
  output logic [NumCoresPerTile-1:0][idx_width(NumRemoteReqPortsPerTile)-1:0] remote_req_interco_tgt_sel_o

);

  /****************
   *   Includes   *
   ****************/

  `include "common_cells/registers.svh"

  /*****************
   *  Definitions  *
   *****************/
  `define min(a,b) (((a) < (b))? (a) : (b))
  `define max(a,b) (((a) > (b))? (a) : (b))

  typedef logic [idx_width(NumRemoteReqPortsPerTile)-1:0] remote_ports_index_t;
  
  localparam SHIFT_AMOUNT = `min(TCDMAddrMemWidth, idx_width(NumBanksPerTile)); // or 4
  localparam RemoteReqBits = `max(1, $clog2(NumRemoteReqPortsPerTile-1));

  function automatic logic [idx_width(NumBanksPerTile)-1:0] spm_bank_id_remap (
      logic [idx_width(NumBanksPerTile)-1:0] data_in,
      logic [SHIFT_AMOUNT-1:0] idx_i
  );
  `ifdef SPM_BANK_ID_REMAP
      spm_bank_id_remap = data_in + idx_i;
  `else
      spm_bank_id_remap = data_in;
  `endif
  endfunction



  /************************
   *  Bank Address Remap  *
   ************************/
  tcdm_dma_req_t                               tcdm_dma_req_remapped;
  tcdm_slave_req_t [NumRemoteReqPortsPerTile-1:0] tcdm_slave_req_remapped;
  tcdm_slave_req_t [NumCoresPerTile-1:0]       local_req_interco_payload_remapped;


  always_comb begin
    tcdm_dma_req_remapped = tcdm_dma_req_i;
    tcdm_dma_req_remapped.tgt_addr[idx_width(NumBanksPerTile)-1:0] = 
      spm_bank_id_remap(
        tcdm_dma_req_i.tgt_addr[idx_width(NumBanksPerTile)-1:0],
        tcdm_dma_req_i.tgt_addr[idx_width(NumBanksPerTile) +: SHIFT_AMOUNT]
      );

    for(int rp = 0; rp < NumRemoteReqPortsPerTile; rp++) begin
      tcdm_slave_req_remapped[rp] = tcdm_slave_req_i[rp];
      tcdm_slave_req_remapped[rp].tgt_addr[idx_width(NumBanksPerTile)-1:0] = 
        spm_bank_id_remap(
        tcdm_slave_req_i[rp].tgt_addr[idx_width(NumBanksPerTile)-1:0],
        tcdm_slave_req_i[rp].tgt_addr[idx_width(NumBanksPerTile) +: SHIFT_AMOUNT]
        );
    end

    for(int c = 0; c < NumCoresPerTile; c++) begin
      local_req_interco_payload_remapped[c] = local_req_interco_payload_i[c];
      local_req_interco_payload_remapped[c].tgt_addr[idx_width(NumBanksPerTile)-1:0] = 
        spm_bank_id_remap(
        local_req_interco_payload_i[c].tgt_addr[idx_width(NumBanksPerTile)-1:0],
        local_req_interco_payload_i[c].tgt_addr[idx_width(NumBanksPerTile) +: SHIFT_AMOUNT]
        );
    end
  end

  assign tcdm_dma_req_remapped_o              = tcdm_dma_req_remapped;
  assign tcdm_slave_req_remapped_o            = tcdm_slave_req_remapped;
  assign local_req_interco_payload_remapped_o = local_req_interco_payload_remapped;

  /****************************
   *   Remote Interconnects   *
   ****************************/
  logic                [NumCoresPerTile-1:0] remote_req_interco_hsk;
  logic                [NumCoresPerTile-1:0] remote_req_interco_hsk_q;
  group_id_t           [NumCoresPerTile-1:0] tgt_group_id;
  logic                [NumCoresPerTile-1:0] group_id_is_local;
  // remote_ports_index_t [NumCoresPerTile-1:0] remote_req_interco_tgt_sel_q;
  // logic                [NumCoresPerTile-1:0] remote_req_interco_tgt_sel_q_update;

  logic                [NumCoresPerTile-1:0] remote_req_interco_valid_mask_local;
  logic                [NumCoresPerTile-1:0][RemoteReqBits-1:0] remote_req_interco_tgt_sel_mask_local;
  logic                [NumCoresPerTile-1:0] remote_req_interco_tgt_sel_mask_local_vld;
  remote_ports_index_t [NumCoresPerTile-1:0] remote_req_interco_tgt_sel_shift_local;

  logic                [NumCoresPerTile-1:0] remote_req_interco_to_xbar_valid;
  logic                [NumCoresPerTile-1:0] remote_req_interco_to_xbar_valid_q;
  logic                [NumCoresPerTile-1:0] remote_req_interco_to_xbar_ready;


  for(genvar c = 0; c < NumCoresPerTile; c++) begin: gen_remote_req_interco_handle_local
    assign group_id_is_local[c] = tgt_group_id[c] == group_id_i;

    assign remote_req_interco_valid_mask_local[c] = group_id_is_local[c] ? 0 : remote_req_interco_valid_i[c];


    assign remote_req_interco_tgt_sel_shift_local[c] = 
    {{($bits(remote_ports_index_t) - RemoteReqBits){1'b0}}, remote_req_interco_tgt_sel_mask_local[c]} + 1;

    // assign remote_req_interco_to_xbar_valid[c] = group_id_is_local[c] ? remote_req_interco_valid_i[c] :
    //                                              remote_req_interco_tgt_sel_mask_local_vld[c];
    assign remote_req_interco_to_xbar_valid[c] = remote_req_interco_valid_i[c];
    // assign remote_req_interco_to_xbar_ready[c] = group_id_is_local[c] ? remote_req_interco_ready_i[c] :
    //                                              remote_req_interco_tgt_sel_mask_local_vld[c] & remote_req_interco_ready_i[c];
    assign remote_req_interco_to_xbar_ready[c] = remote_req_interco_ready_i[c];

    assign remote_req_interco_hsk[c] = remote_req_interco_to_xbar_valid[c] & remote_req_interco_to_xbar_ready[c];
    // assign remote_req_interco_tgt_sel_q_update[c] = (remote_req_interco_hsk_q[c] & remote_req_interco_to_xbar_valid[c]) |
    //                                                 (~remote_req_interco_to_xbar_valid_q[c] & remote_req_interco_to_xbar_valid[c]);

    `FF(remote_req_interco_hsk_q[c], remote_req_interco_hsk[c], '0, clk_i, rst_ni);
    `FF(remote_req_interco_to_xbar_valid_q[c], remote_req_interco_to_xbar_valid[c], '0, clk_i, rst_ni);
    // `FFLARN(remote_req_interco_tgt_sel_q[c], remote_req_interco_tgt_sel_i[c], remote_req_interco_tgt_sel_q_update[c], '0, clk_i, rst_ni);
  end: gen_remote_req_interco_handle_local

  assign remote_req_interco_to_xbar_valid_o = remote_req_interco_to_xbar_valid;
  assign remote_req_interco_to_xbar_ready_o = remote_req_interco_to_xbar_ready;

  logic [$clog2(NumCoresPerTile)-1:0] priority_d, priority_q;
  assign priority_d = (priority_q == (NumCoresPerTile-1)) ? '0 : priority_q + 1;
  `FF(priority_q, priority_d, '0, clk_i, rst_ni);

`ifdef DYNAMIC_PORT_ALLOC
  selector #(
    .InNum    (NumCoresPerTile),
    .OutNum   (NumRemoteReqPortsPerTile-1)
  ) i_selector (
    .req_vector_i             (remote_req_interco_valid_mask_local),
    .priority_i               (priority_q               ),
    .sel_inport_idx_o         (                         ),
    .asn_outport_idx_o        (remote_req_interco_tgt_sel_mask_local),
    .asn_outport_vld_o        (remote_req_interco_tgt_sel_mask_local_vld)
  );
`else
  assign remote_req_interco_tgt_sel_mask_local = '0;
  assign remote_req_interco_tgt_sel_mask_local_vld = '0;
`endif


  /*******************
   *   Core De/mux   *
   *******************/
  for (genvar c = 0; c < NumCoresPerTile; c++) begin: gen_core_mux
    assign tgt_group_id[c] = prescramble_tcdm_req_tgt_addr_i[c][ByteOffset + $clog2(NumBanksPerTile) + $clog2(NumTilesPerGroup) +: $clog2(NumGroups)];

    // Map the requests from cores to the 
    // channels with different usage:
    //                                 port id
    // ------     ------   -> local    [ 0 (lsb for local port)
    // |    | ->  |    |   -> r     Low  1
    // |Tile| ->  |xbar|   -> r     ||   2
    // |    | ->  |    |   -> rw    ||   3
    // |    | ->  |    |   -> w     \/   4
    // ------     ------   -> w    High   5 ]
    if((NumRdRemoteReqPortsPerTile > 0) || (NumWrRemoteReqPortsPerTile > 0)) begin
      assign remote_req_interco_tgt_sel_o[c] = group_id_is_local[c] ? 0 : 
                                              ~(remote_req_interco_wen_i[c] | remote_req_interco_amoen_i[c]) ? 
                                               (1 + (c % (NumRdRemoteReqPortsPerTile + NumRdWrRemoteReqPortsPerTile))) :
                                               (1 + NumRdRemoteReqPortsPerTile + (c % (NumWideRemoteReqPortsPerTile)));
    end else begin
      assign remote_req_interco_tgt_sel_o[c] = group_id_is_local[c] ? 0 : (1 + (c % (NumRemoteReqPortsPerTile - 1)));
      // assign remote_req_interco_tgt_sel_o[c] = group_id_is_local[c] ? 0 :
      //                                       //  ~remote_req_interco_tgt_sel_q_update[c] ? remote_req_interco_tgt_sel_q[c] :
      //                                        (remote_req_interco_to_xbar_valid[c] ? remote_req_interco_tgt_sel_shift_local[c] :
      //                                        (1 + (c % (NumRemoteReqPortsPerTile - 1))));
    end
  end
endmodule
