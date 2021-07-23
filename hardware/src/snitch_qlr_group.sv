// Copyright 2021 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

/// Description: Instantiates Queue Linked Registers (QLRs) which act as intermediates between
/// the queue system and the register file. Access to the request and the response port of the
/// LSU are multiplexed between QLRs and Snitch/LSU, respectively. Round-robin arbiters guarantee
/// fairness between the QLRs.

/// Author: Gua Hao Khov <khovg@student.ethz.ch>

module snitch_qlr_group
  import mempool_pkg::*;
  import cf_math_pkg::idx_width;
#(
  parameter int unsigned NumWritePorts  = 2,
  parameter type         tag_t          = logic [4:0],
  // Dependent parameters. DO NOT CHANGE.
  localparam int unsigned BankAddrWidth = idx_width(NumBanks),
  localparam int unsigned SeqAddrBits   = $clog2(SeqMemSizePerTile),
  localparam int unsigned RemAddrBits   = (AddrWidth - SeqAddrBits),
  localparam int unsigned BankSelBits   = $clog2(NumBanksPerTile),
  localparam int unsigned TileSelBits   = (BankAddrWidth - BankSelBits)
) (
  input  logic                                    clk_i,
  input  logic                                    rst_ni,
  // LSU request input (from Snitch)
  input  tag_t                                    lsu_qtag_i,    // register tag
  input  logic                                    lsu_qwrite_i,  // write bit
  input  logic                                    lsu_qsigned_i, // signed bit
  input  logic [AddrWidth-1:0]                    lsu_qaddr_i,   // address
  input  logic [DataWidth-1:0]                    lsu_qdata_i,   // data
  input  logic [1:0]                              lsu_qsize_i,   // data size
  input  logic [3:0]                              lsu_qamo_i,    // AMO code
  input  logic                                    lsu_qvalid_i,  // valid bit
  output logic                                    lsu_qready_o,  // ready bit
  // LSU request output (to LSU)
  output tag_t                                    lsu_out_tag_o,    // register tag
  output logic                                    lsu_out_write_o,  // write bit
  output logic                                    lsu_out_signed_o, // signed bit
  output logic [AddrWidth-1:0]                    lsu_out_addr_o,   // address
  output logic [DataWidth-1:0]                    lsu_out_data_o,   // data
  output logic [1:0]                              lsu_out_size_o,   // data size
  output logic [3:0]                              lsu_out_amo_o,    // AMO code
  output logic                                    lsu_out_qlr_o,    // request from QLR bit
  output logic                                    lsu_out_valid_o,  // valid bit
  input  logic                                    lsu_out_ready_i,  // ready bit
  // LSU response input (from LSU)
  input  logic [DataWidth-1:0]                    lsu_in_data_i,  // data
  input  tag_t                                    lsu_in_tag_i,   // register tag
  input  logic                                    lsu_in_error_i, // error bit
  input  logic                                    lsu_in_qlr_i,   // request from QLR bit
  input  logic                                    lsu_in_valid_i, // valid bit
  output logic                                    lsu_in_ready_o, // ready bit
  // LSU response output (to Snitch)
  output logic [DataWidth-1:0]                    lsu_pdata_o,  // data
  output tag_t                                    lsu_ptag_o,   // register tag
  output logic                                    lsu_perror_o, // error bit
  output logic                                    lsu_pvalid_o, // valid bit
  input  logic                                    lsu_pready_i, // ready bit
  // Instruction snoop interface
  input  tag_t                                    instr_rs1_i,       // rs1 tag
  input  tag_t                                    instr_rs2_i,       // rs2 tag
  input  tag_t                                    instr_rd_i,        // rd tag
  input  logic                                    instr_reads_rs1_i, // rs1 usage bit
  input  logic                                    instr_reads_rs2_i, // rs2 usage bit
  input  logic                                    instr_reads_rd_i,  // rd usage bit
  input  logic                                    instr_executed_i,  // execution bit
  // scoreboard interface
  output logic [NumQlrsPerCore-1:0]               qlr_sb_enabled_o, // QLR scoreboard enable
  output logic [NumQlrsPerCore-1:0]               qlr_sb_o,         // QLR scoreboard bit
  // RF snoop interface
  input  logic [NumWritePorts-1:0][DataWidth-1:0] rf_in_data_i, // data
  input  tag_t [NumWritePorts-1:0]                rf_in_tag_i,  // register tag
  input  logic [NumWritePorts-1:0]                rf_in_vld_i,  // valid bit
  // stall signal
  output logic [NumQlrsPerCore-1:0]               qlr_ready_o // instruction stall
);

  // ----------------
  // TYPEDEFS
  // ----------------

  typedef logic [DataWidth-1:0]     data_t;
  typedef logic [BankAddrWidth-1:0] bank_addr_t;
  typedef logic [3:0]               amo_code_t;

  typedef struct packed {
    data_t      data;
    bank_addr_t bank_addr;
    tag_t       tag;
    amo_code_t  amo;
  } lsu_request_t;

  typedef struct packed {
    data_t data;
    tag_t  tag;
  } lsu_response_t;

  // ----------------
  // ENUMERATIONS
  // ----------------

  typedef enum logic [1:0] {
    Byte = 2'b00,
    HalfWord = 2'b01,
    Word = 2'b10,
    Double = 2'b11
  } size_e;

  // ----------------
  // SIGNALS
  // ----------------

  // QLR instances
  lsu_request_t [NumQlrsPerCore-1:0]  qlr_lsu_out;
  logic [NumQlrsPerCore-1:0]          qlr_lsu_out_req;
  logic [NumQlrsPerCore-1:0]          qlr_lsu_out_gnt;
  logic                               qlr_lsu_in_vld;
  lsu_response_t [NumQlrsPerCore-1:0] qlr_rf_out;
  logic [NumQlrsPerCore-1:0]          qlr_rf_out_req;
  logic [NumQlrsPerCore-1:0]          qlr_rf_out_gnt;

  // Configuration
  logic [DataWidth-1:0]      cfg_data;
  tag_t                      cfg_tag;
  logic [2:0]                cfg_addr;
  logic                      cfg_match;
  logic                      cfg_vld;
  logic [NumQlrsPerCore-1:0] cfg_rdy;

  // Address construction
  logic [BankSelBits-1:0] qlr_req_bank_sel;
  logic [TileSelBits-1:0] qlr_req_tile_sel;
  logic [SeqAddrBits-1:0] qlr_req_seq_addr;
  logic [RemAddrBits-1:0] qlr_req_rem_addr;
  logic [AddrWidth-1:0]   qlr_req_full_addr;

  // LSU request arbitration
  logic         qlr_req_valid;
  logic         qlr_req_select;
  logic         qlr_req_gnt;
  logic         qlr_req_lock_d, qlr_req_lock_q;
  lsu_request_t qlr_req;

  // LSU response arbitration
  logic          qlr_resp_valid;
  logic          qlr_resp_select;
  logic          qlr_resp_gnt;
  lsu_response_t qlr_resp;

  // Stall signal
  logic [NumQlrsPerCore-1:0] qlr_fifo_stall;

  // ----------------
  // QLR INSTANCES
  // ----------------

  for (genvar ii = 0; ii < NumQlrsPerCore; ii++) begin : gen_qlrs
    snitch_qlr #(
      .DataWidth     ( DataWidth      ),
      .BankAddrWidth ( BankAddrWidth  ),
      .NumWritePorts ( NumWritePorts  ),
      .FifoSize      ( QlrFifoSize    ),
      .MaxRequests   ( QlrMaxRequests ),
      .MaxRfReads    ( QlrMaxRfReads  ),
      .tag_t         ( tag_t          ),
      .AssignedTag   ( QlrTags[ii]    )
    ) i_qlr (
      .clk_i                                         ,
      .rst_ni                                        ,
      .cfg_data_i       ( cfg_data                  ),
      .cfg_tag_i        ( cfg_tag                   ),
      .cfg_addr_i       ( cfg_addr                  ),
      .cfg_vld_i        ( cfg_vld                   ),
      .cfg_rdy_o        ( cfg_rdy[ii]               ),
      .lsu_out_data_o   ( qlr_lsu_out[ii].data      ),
      .lsu_out_addr_o   ( qlr_lsu_out[ii].bank_addr ),
      .lsu_out_tag_o    ( qlr_lsu_out[ii].tag       ),
      .lsu_out_amo_o    ( qlr_lsu_out[ii].amo       ),
      .lsu_out_req_o    ( qlr_lsu_out_req[ii]       ),
      .lsu_out_gnt_i    ( qlr_lsu_out_gnt[ii]       ),
      .lsu_in_data_i                                 ,
      .lsu_in_tag_i                                  ,
      .lsu_in_vld_i     ( qlr_lsu_in_vld            ),
      .instr_rs1_i                                   ,
      .instr_rs2_i                                   ,
      .instr_rd_i                                    ,
      .instr_reads_rs1_i                             ,
      .instr_reads_rs2_i                             ,
      .instr_reads_rd_i                              ,
      .instr_executed_i                              ,
      .qlr_sb_enabled_o ( qlr_sb_enabled_o[ii]      ),
      .qlr_sb_o         ( qlr_sb_o[ii]              ),
      .rf_in_data_i                                  ,
      .rf_in_tag_i                                   ,
      .rf_in_vld_i                                   ,
      .rf_out_data_o    ( qlr_rf_out[ii].data       ),
      .rf_out_tag_o     ( qlr_rf_out[ii].tag        ),
      .rf_out_req_o     ( qlr_rf_out_req[ii]        ),
      .rf_out_gnt_i     ( qlr_rf_out_gnt[ii]        ),
      .qlr_fifo_stall_o ( qlr_fifo_stall[ii]        )
    );
  end

  // LSU response is only valid for QLR if request came from QLR
  assign qlr_lsu_in_vld = lsu_in_valid_i & lsu_in_qlr_i;

  // ----------------
  // CONFIGURATION
  // ----------------
  // Configuration is identifiable via a specific address mask
  assign cfg_match = (lsu_qaddr_i ==? QlrConfigMask);
  assign cfg_vld   = lsu_qvalid_i & cfg_match;

  // LSBs of address are used to target specific QLR and config
  assign cfg_tag  = lsu_qaddr_i[5+:$bits(tag_t)];
  assign cfg_addr = lsu_qaddr_i[2+:3];

  // Configuration data is passed through the store data
  assign cfg_data = lsu_qdata_i;

  // ----------------
  // ADDR CONSTRUCT
  // ----------------
  // Based on bank address construct the actual address
  // Split bank address into tile ID and local bank select
  // Sequential address part contains the local bank select
  // Non-sequential address part contains the tile ID
  assign qlr_req_bank_sel  = qlr_req.bank_addr[BankSelBits-1:0];
  assign qlr_req_tile_sel  = qlr_req.bank_addr[BankAddrWidth-1:BankSelBits];
  assign qlr_req_seq_addr  = {'b0, qlr_req_bank_sel, 2'b0};
  assign qlr_req_rem_addr  = {'b0, qlr_req_tile_sel};
  assign qlr_req_full_addr = {qlr_req_rem_addr, qlr_req_seq_addr};

  // ----------------
  // LSU REQUEST ARB
  // ----------------

  rr_arb_tree #(
    .NumIn     ( NumQlrsPerCore ),
    .DataType  ( lsu_request_t  ),
    .AxiVldRdy ( 1'b1           ),
    .LockIn    ( 1'b1           )
  ) i_req_arb (
    .clk_i                      ,
    .rst_ni                     ,
    .flush_i ( 1'b0            ),
    .rr_i    ( '0              ),
    .req_i   ( qlr_lsu_out_req ),
    .gnt_o   ( qlr_lsu_out_gnt ),
    .data_i  ( qlr_lsu_out     ),
    .req_o   ( qlr_req_valid   ),
    .gnt_i   ( qlr_req_gnt     ),
    .data_o  ( qlr_req         ),
    .idx_o   (                 )
  );

  // Grant QLRs access to LSU request port if LSU is ready and Snitch does not use it
  // (Snitch configures QLRs with store instructions which get intercepted and thus
  // the LSU request port is not actually used by Snitch during configuration)
  // (in case of valid QLR request lock in qlr_req_select until granted)
  assign qlr_req_select = ~(lsu_qvalid_i & ~cfg_match) | qlr_req_lock_q;
  assign qlr_req_gnt    = qlr_req_valid & lsu_out_ready_i & qlr_req_select;

  // Multiplex LSU request port between QLRs and Snitch
  assign lsu_out_tag_o    = qlr_req_select ? qlr_req.tag       : lsu_qtag_i;
  assign lsu_out_write_o  = qlr_req_select ? 1'b0              : lsu_qwrite_i;
  assign lsu_out_signed_o = qlr_req_select ? 1'b0              : lsu_qsigned_i;
  assign lsu_out_addr_o   = qlr_req_select ? qlr_req_full_addr : lsu_qaddr_i;
  assign lsu_out_data_o   = qlr_req_select ? qlr_req.data      : lsu_qdata_i;
  assign lsu_out_size_o   = qlr_req_select ? Word              : lsu_qsize_i;
  assign lsu_out_amo_o    = qlr_req_select ? qlr_req.amo       : lsu_qamo_i;
  assign lsu_out_qlr_o    = qlr_req_select ? 1'b1              : 1'b0;
  assign lsu_out_valid_o  = qlr_req_select ? qlr_req_valid     : lsu_qvalid_i;

  // Lock valid QLR requests if set to serve QLR requests
  // (requests to LSU must remain stable so switch back to Snitch only once granted)
  assign qlr_req_lock_d = qlr_req_select & (qlr_req_valid & ~lsu_out_ready_i);

  // ----------------
  // LSU RESPONSE ARB
  // ----------------

  rr_arb_tree #(
    .NumIn     ( NumQlrsPerCore ),
    .DataType  ( lsu_response_t ),
    .AxiVldRdy ( 1'b1           ),
    .LockIn    ( 1'b1           )
  ) i_rf_arb (
    .clk_i                     ,
    .rst_ni                    ,
    .flush_i ( 1'b0           ),
    .rr_i    ( '0             ),
    .req_i   ( qlr_rf_out_req ),
    .gnt_o   ( qlr_rf_out_gnt ),
    .data_i  ( qlr_rf_out     ),
    .req_o   ( qlr_resp_valid ),
    .gnt_i   ( qlr_resp_gnt   ),
    .data_o  ( qlr_resp       ),
    .idx_o   (                )
  );

  // Grant QLRs access to LSU response port if Snitch is ready and LSU does not use it
  // (LSU provides data to QLRs with the same port as its normal responses which is then
  // intercepted by the QLRs and does not actually go through the actual response port)
  assign qlr_resp_select = ~(lsu_in_valid_i & ~lsu_in_qlr_i);
  assign qlr_resp_gnt    = qlr_resp_valid & lsu_pready_i & qlr_resp_select;

  // Multiplex LSU request port between QLRs and Snitch
  assign lsu_pdata_o  = qlr_resp_select ? qlr_resp.data  : lsu_in_data_i;
  assign lsu_ptag_o   = qlr_resp_select ? qlr_resp.tag   : lsu_in_tag_i;
  assign lsu_perror_o = qlr_resp_select ? 1'b0           : lsu_in_error_i;
  assign lsu_pvalid_o = qlr_resp_select ? qlr_resp_valid : lsu_in_valid_i;

  // ----------------
  // READY SIGNALS
  // ----------------

  // QLRs are always ready for a LSU response targeted towards them, but
  // re-order buffer demands ready to only be set if also valid is set
  // If RF does not service QLRs then pass along the ready signal from RF
  assign lsu_in_ready_o = qlr_resp_select ? lsu_in_valid_i : lsu_pready_i;

  // LSU ready signal to Snitch
  always_comb begin
    // Check if QLR or Snitch has control over LSU request port
    if (qlr_req_select == 1'b1) begin
      // If QLR has control Snitch could still be configuring QLR
      if (cfg_match == 1'b1) begin
        // QLR configuration demands all QLRs to be ready for it
        // (QLRs not targeted by configuration have their ready set to 1'b1)
        lsu_qready_o = &cfg_rdy;
      end else begin
        // If Snitch has neither control nor is configuring sent back 1'b0
        lsu_qready_o = 1'b0;
      end
    end else begin
      // Snitch has control over the LSU request port
      lsu_qready_o = lsu_out_ready_i;
    end
  end

  // ----------------
  // STALL SIGNAL
  // ----------------
  // QLRs are ready if there is no stall due to a full FIFO
  assign qlr_ready_o = ~qlr_fifo_stall;

  // ----------------
  // SEQUENTIAL
  // ----------------
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      qlr_req_lock_q <= 1'b0;
    end else begin
      qlr_req_lock_q <= qlr_req_lock_d;
    end
  end

  // ----------------
  // ASSERTIONS
  // ----------------
  // pragma translate_off
  // Check for unsupported parameters
  if (DataWidth != 32) begin
    $error($sformatf("Module currently only supports DataWidth = 32. DataWidth is currently set to: %0d", DataWidth));
  end

  `ifndef VERILATOR
    cfg_valid_tag : assert property(
      @(posedge clk_i) disable iff (~rst_ni)
      (cfg_vld |-> (cfg_tag inside {QlrTags[0], QlrTags[1], QlrTags[2], QlrTags[3]})))
      else $fatal (1, "Configuration targets invalid QLR register tag");
  `endif
  // pragma translate_on

endmodule
