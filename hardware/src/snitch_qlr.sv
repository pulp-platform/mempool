// Copyright 2021 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

/// Description: A Queue Linked Register (QLR) acts as an intermediate between the queue system
/// in the tcdm_adapter and the register file. It supports incoming queues by constantly
/// requesting queue pops and storing the popped data in its FIFO to later update the register
/// file when necessary. It supports outgoing queues by catching writes to the register file,
/// storing the write data in its FIFO to be later pushed into the queue. A combination of both
/// in form of in/out QLRs is also supported which passed popped data along to an outgoing queue.
/// QLRs allow us to use the queue system via register file accesses instead of LSU instructions.

/// Author: Gua Hao Khov <khovg@student.ethz.ch>

module snitch_qlr
  import cf_math_pkg::idx_width;
#(
  parameter int unsigned DataWidth     = 32,
  parameter int unsigned BankAddrWidth = 10,
  parameter int unsigned NumWritePorts = 2,
  parameter int unsigned FifoSize      = 4,
  parameter int unsigned MaxRequests   = 4096,
  parameter int unsigned MaxRfReads    = 8,
  parameter type         tag_t         = logic [4:0],
  parameter tag_t        AssignedTag   = 5'b00000,
  // Dependent parameters. DO NOT CHANGE.
  localparam int unsigned ReqCntWidth  = idx_width(MaxRequests + 1),
  localparam int unsigned RfCntWidth   = idx_width(MaxRfReads + 1)
) (
  input  logic                                    clk_i,
  input  logic                                    rst_ni,
  // configuration interface
  input  logic [DataWidth-1:0]                    cfg_data_i, // data
  input  tag_t                                    cfg_tag_i,  // register tag
  input  logic [2:0]                              cfg_addr_i, // address
  input  logic                                    cfg_vld_i,  // valid bit
  output logic                                    cfg_rdy_o,  // ready bit
  // LSU request interface
  output logic [DataWidth-1:0]                    lsu_out_data_o, // data
  output logic [BankAddrWidth-1:0]                lsu_out_addr_o, // address
  output tag_t                                    lsu_out_tag_o,  // register tag
  output logic [3:0]                              lsu_out_amo_o,  // AMO code
  output logic                                    lsu_out_req_o,  // request bit
  input  logic                                    lsu_out_gnt_i,  // grant bit
  // LSU response interface
  input  logic [DataWidth-1:0]                    lsu_in_data_i, // data
  input  tag_t                                    lsu_in_tag_i,  // register tag
  input  logic                                    lsu_in_vld_i,  // valid bit
  // instruction snoop interface
  input  tag_t                                    instr_rs1_i,       // rs1 tag
  input  tag_t                                    instr_rs2_i,       // rs2 tag
  input  tag_t                                    instr_rd_i,        // rd tag
  input  logic                                    instr_reads_rs1_i, // rs1 usage bit
  input  logic                                    instr_reads_rs2_i, // rs2 usage bit
  input  logic                                    instr_reads_rd_i,  // rd usage bit
  input  logic                                    instr_executed_i,  // execution bit
  // scoreboard interface
  output logic                                    qlr_sb_enabled_o, // QLR scoreboard enable
  output logic                                    qlr_sb_o,         // QLR scoreboard bit
  // RF snoop interface
  input  logic [NumWritePorts-1:0][DataWidth-1:0] rf_in_data_i, // data
  input  tag_t [NumWritePorts-1:0]                rf_in_tag_i,  // register tag
  input  logic [NumWritePorts-1:0]                rf_in_vld_i,  // valid bit
  // RF request interface
  output logic [DataWidth-1:0]                    rf_out_data_o, // data
  output tag_t                                    rf_out_tag_o,  // register tag
  output logic                                    rf_out_req_o,  // request bit
  input  logic                                    rf_out_gnt_i,  // grant bit
  // stall signal
  output logic                                    qlr_fifo_stall_o // FIFO stall
);

  // ----------------
  // ENUMERATIONS
  // ----------------

  typedef enum logic [2:0] {
      CfgType     = 3'b000, // IQLR & OQLR (QLR type)
      CfgReqCount = 3'b010, // Number of requests
      CfgRfCount  = 3'b011, // Number or RF accesses
      CfgInAddr   = 3'b100, // IQLR bank address
      CfgOutAddr  = 3'b101  // OQLR bank address
  } cfg_addr_e;

  typedef enum logic [3:0] {
      AMONone = 4'h0,
      AMOSwap = 4'h1,
      AMOAdd  = 4'h2,
      AMOAnd  = 4'h3,
      AMOOr   = 4'h4,
      AMOXor  = 4'h5,
      AMOMax  = 4'h6,
      AMOMaxu = 4'h7,
      AMOMin  = 4'h8,
      AMOMinu = 4'h9,
      AMOLR   = 4'hA,
      AMOSC   = 4'hB,
      QPush   = 4'hC,
      QPop    = 4'hD
  } amo_op_e;

  typedef enum logic [2:0] {
    ReqIdle, ReqPop, AwaitPop, ReqPush, AwaitPush
  } req_fsm_state_e;

  typedef enum logic [1:0] {
    RFIdle, UpdateRF, SnoopInstr
  } rf_fsm_state_e;

  // ----------------
  // SIGNALS
  // ----------------

  // FIFO
  logic                 fifo_full;
  logic                 fifo_empty;
  logic                 fifo_flush;
  logic                 fifo_push;
  logic                 fifo_pop;
  logic [DataWidth-1:0] fifo_in;
  logic [DataWidth-1:0] fifo_out;
  logic                 fifo_iqlr_pop_stall_d, fifo_iqlr_pop_stall_q;
  logic                 fifo_oqlr_pop_stall_d, fifo_oqlr_pop_stall_q;
  logic                 fifo_ioqlr_pop;

  // QLR type (incoming & outgoing)
  logic iqlr_enabled_d, iqlr_enabled_q;
  logic oqlr_enabled_d, oqlr_enabled_q;

  // Configuration
  logic                     cfg_req_vld;
  logic                     qlr_idle;
  logic                     iqlr_start;
  logic                     oqlr_start;
  logic [ReqCntWidth-1:0]   req_cntr_max_d, req_cntr_max_q;
  logic [RfCntWidth-1:0]    rf_cntr_max_d, rf_cntr_max_q;
  logic [BankAddrWidth-1:0] iqlr_addr_d, iqlr_addr_q;
  logic [BankAddrWidth-1:0] oqlr_addr_d, oqlr_addr_q;

  // LSU request
  req_fsm_state_e                  req_fsm_state_d, req_fsm_state_q;
  logic unsigned [ReqCntWidth-1:0] req_fsm_cntr_d, req_fsm_cntr_q;
  logic                            req_fsm_qpop_resp;
  logic                            req_fsm_qpush_resp;

  // LSU response
  logic lsu_resp_vld;

  // RF snoop
  logic [DataWidth-1:0] rf_snoop_data;
  logic                 rf_snoop_data_vld;
  logic [1:0]           rf_snoop_match;
  logic [1:0]           rf_snoop_vld;

  // Instr snoop
  logic instr_reads_qlr;

  // RF request
  rf_fsm_state_e                  rf_fsm_state_d, rf_fsm_state_q;
  logic unsigned [RfCntWidth-1:0] rf_fsm_cntr_d, rf_fsm_cntr_q;

  // ----------------
  // FIFO
  // ----------------
  fifo_v3 #(
    .FALL_THROUGH ( 0         ),
    .DATA_WIDTH   ( DataWidth ),
    .DEPTH        ( FifoSize  )
  ) i_fifo (
    .clk_i                    ,
    .rst_ni                   ,
    .testmode_i ( 1'b0       ),
    .flush_i    ( fifo_flush ),
    .full_o     ( fifo_full  ),
    .empty_o    ( fifo_empty ),
    .usage_o    (            ),
    .data_i     ( fifo_in    ),
    .push_i     ( fifo_push  ),
    .data_o     ( fifo_out   ),
    .pop_i      ( fifo_pop   )
  );

  // FIFO input
  assign fifo_in   = iqlr_enabled_q ? lsu_in_data_i     : rf_snoop_data;
  assign fifo_push = iqlr_enabled_q ? req_fsm_qpop_resp : rf_snoop_data_vld;

  // Stall of FIFO pop for in/out QLRs
  always_comb begin
    // FIFO pop for in/out QLRs has both conditions (RF and QPush request)
    // (if only one is met FIFO pop is stalled until other one arrives)
    if (fifo_oqlr_pop_stall_q == 1'b0) begin
      fifo_oqlr_pop_stall_d = req_fsm_qpush_resp & ~fifo_pop;
    end else begin
      fifo_oqlr_pop_stall_d = ~fifo_pop;
    end
    if (fifo_iqlr_pop_stall_q == 1'b0) begin
      fifo_iqlr_pop_stall_d = rf_out_gnt_i & ~fifo_pop;
    end else begin
      fifo_iqlr_pop_stall_d = ~fifo_pop;
    end

    // FIFO pop for in/out QLRs requires only one condition if previously stalled
    // (req_fsm and rf_fsm guarantee that the same condition does not arrive twice)
    if (fifo_iqlr_pop_stall_q | fifo_oqlr_pop_stall_q) begin
      fifo_ioqlr_pop = req_fsm_qpush_resp | rf_out_gnt_i;
    end else begin
      fifo_ioqlr_pop = req_fsm_qpush_resp & rf_out_gnt_i;
    end
  end

  // FIFO pop
  always_comb begin
    // Select the FIFO pop
    unique case ({iqlr_enabled_q, oqlr_enabled_q})
      2'b00:   fifo_pop = 1'b0;
      2'b01:   fifo_pop = req_fsm_qpush_resp;
      2'b10:   fifo_pop = rf_out_gnt_i;
      2'b11:   fifo_pop = fifo_ioqlr_pop;
      default: fifo_pop = 1'b0;
    endcase
  end

  // Flush FIFO if idle
  assign fifo_flush = (req_fsm_state_q == ReqIdle) & (rf_fsm_state_q == RFIdle);

  // ----------------
  // CONFIGURATION
  // ----------------
  // Configuration request only valid if register tag also matches
  assign cfg_req_vld = cfg_vld_i & (cfg_tag_i == AssignedTag);

  // Only accept configuration request if idle (default is 1'b1 to facilitate merge of rdy signals)
  assign qlr_idle  = (req_fsm_state_q == ReqIdle) & (rf_fsm_state_q == RFIdle);
  assign cfg_rdy_o = cfg_req_vld ? qlr_idle : 1'b1;

  // Configuration of QLR
  always_comb begin
    // Default
    req_cntr_max_d = req_cntr_max_q;
    rf_cntr_max_d  = rf_cntr_max_q;
    iqlr_addr_d    = iqlr_addr_q;
    oqlr_addr_d    = oqlr_addr_q;

    // Default start signals for FSMs
    iqlr_start = 1'b0;
    oqlr_start = 1'b0;

    // Accept configuration on handshake
    if (cfg_req_vld & cfg_rdy_o) begin
      unique case (cfg_addr_e'(cfg_addr_i))
        CfgType: begin
          iqlr_start = cfg_data_i[0];
          oqlr_start = cfg_data_i[1];
        end
        CfgReqCount: req_cntr_max_d = cfg_data_i[ReqCntWidth-1:0];
        CfgRfCount:  rf_cntr_max_d  = cfg_data_i[RfCntWidth-1:0];
        CfgInAddr:   iqlr_addr_d    = cfg_data_i[BankAddrWidth-1:0];
        CfgOutAddr:  oqlr_addr_d    = cfg_data_i[BankAddrWidth-1:0];
        default:;
      endcase
    end
  end

  // ----------------
  // LSU REQUEST
  // ----------------
  always_comb begin
    // Default
    req_fsm_state_d = req_fsm_state_q;
    req_fsm_cntr_d  = req_fsm_cntr_q;
    iqlr_enabled_d  = iqlr_enabled_q;
    oqlr_enabled_d  = oqlr_enabled_q;

    // Data passthrough from FIFO
    lsu_out_data_o = fifo_out;

    // Default LSU request (QPop)
    lsu_out_req_o  = 1'b0;
    lsu_out_tag_o  = AssignedTag;
    lsu_out_amo_o  = QPop;
    lsu_out_addr_o = iqlr_addr_q;

    // Default queue operation responses
    // (set if corresponding response arrived)
    req_fsm_qpop_resp  = 1'b0;
    req_fsm_qpush_resp = 1'b0;

    // FSM
    unique case (req_fsm_state_q)
      // ReqIdle state resets request counter and waits for the start signals
      ReqIdle: begin
        req_fsm_cntr_d = 0;
        // Stores the QLR type started (incoming/outgoing)
        // (Set enable bits to 1'b0 until start signal arrives)
        // (IQLR remains enabled until rf_fsm also arrived in Idle)
        if (rf_fsm_state_q == RFIdle) begin
          iqlr_enabled_d = iqlr_start;
        end
        oqlr_enabled_d = oqlr_start;
        // Transition to corresponding LSU request state
        // (in case of in/out QLRs transition to ReqPop)
        if (iqlr_start == 1'b1) begin
          req_fsm_state_d = ReqPop;
        end else if (oqlr_start == 1'b1) begin
          req_fsm_state_d = ReqPush;
        end
      end

      // ReqPop state requests a QPop from the LSU and
      // once granted transitions to AwaitPop
      ReqPop: begin
        // QPop LSU request
        lsu_out_req_o  = ~fifo_full;
        lsu_out_amo_o  = QPop;
        lsu_out_addr_o = iqlr_addr_q;
        // LSU request granted
        if (lsu_out_gnt_i == 1'b1) begin
          req_fsm_state_d = AwaitPop;
        end
        // Return to ReqIdle once all requests are done
        if (req_fsm_cntr_q == req_cntr_max_q) begin
          lsu_out_req_o   = 1'b0;
          req_fsm_state_d = ReqIdle;
        end
      end

      // AwaitPop state waits for the LSU response, then
      // raises the QPop response flag and transitions out
      AwaitPop: begin
        if (lsu_resp_vld == 1'b1) begin
          // Raise QPop response flag for FIFO control
          req_fsm_qpop_resp = 1'b1;
          // Transition differs for incoming only and in/out QLRs
          if (oqlr_enabled_q == 1'b0) begin
            // Transition back to ReqPop and increment request counter
            req_fsm_cntr_d  = req_fsm_cntr_q + 1;
            req_fsm_state_d = ReqPop;
          end else begin
            // Transition to ReqPush to follow up the QPop with a QPush
            // (increment request counter only after the QPush)
            req_fsm_state_d = ReqPush;
          end
        end
      end

      // RegPush state requests a QPush from the LSU and
      // once granted transitions to AwaitPush
      ReqPush: begin
        // QPush LSU request
        // (for in/out QLRs stall request if FIFO pop stall has not
        // been resolved yet to avoid pushing the same data again)
        lsu_out_req_o  = ~fifo_empty & ~fifo_oqlr_pop_stall_q;
        lsu_out_amo_o  = QPush;
        lsu_out_addr_o = oqlr_addr_q;
        // LSU request granted
        if (lsu_out_gnt_i == 1'b1) begin
          req_fsm_state_d = AwaitPush;
        end
        // Return to ReqIdle once all requests are done
        if (req_fsm_cntr_q == req_cntr_max_q) begin
          lsu_out_req_o   = 1'b0;
          req_fsm_state_d = ReqIdle;
        end
      end

      // AwaitPush state waits for the LSU response, then
      // raises the QPush response flag and transitions out
      AwaitPush: begin
        if (lsu_resp_vld == 1'b1) begin
          // Raise QPush response flag for FIFO control
          req_fsm_qpush_resp = 1'b1;
          // Increment request counter
          req_fsm_cntr_d     = req_fsm_cntr_q + 1;
          // Transition differs for outgoing only and in/out QLRs
          if (iqlr_enabled_q == 1'b0) begin
            // Transition back to ReqPush
            req_fsm_state_d = ReqPush;
          end else begin
            // Transition to ReqPop to request next QPop
            req_fsm_state_d = ReqPop;
          end
        end
      end
      default:;
    endcase
  end

  // ----------------
  // LSU RESPONSE
  // ----------------
  // LSU response only valid if register tag also matches
  assign lsu_resp_vld = lsu_in_vld_i & (lsu_in_tag_i == AssignedTag);

  // ----------------
  // RF SNOOP
  // ----------------
  // If register tag matches and valid is set, the snoop is valid
  for (genvar ii = 0; ii < NumWritePorts; ii++) begin : gen_rf_snoop
    assign rf_snoop_match[ii] = (rf_in_tag_i[ii] == AssignedTag);
    assign rf_snoop_vld[ii]   = rf_snoop_match[ii] & rf_in_vld_i[ii];
  end

  // Switch to data with matched register tag
  always_comb begin
    rf_snoop_data = rf_in_data_i[0];
    for (int ii = 0; ii < NumWritePorts; ii++) begin
      if (rf_snoop_vld[ii] == 1'b1) begin
        rf_snoop_data = rf_in_data_i[ii];
      end
    end
  end

  // RF snooping is only valid if QLR is set to outgoing
  // Data is valid only if one of the RF snoops is valid
  assign rf_snoop_data_vld = oqlr_enabled_q ? |rf_snoop_vld : 1'b0;

  // ----------------
  // INSTR SNOOP
  // ----------------
  // Check if instruction reads the assigned register
  always_comb begin
    instr_reads_qlr = 1'b0;
    if (instr_rs1_i == AssignedTag) begin
      instr_reads_qlr = instr_reads_rs1_i;
    end else if (instr_rs2_i == AssignedTag) begin
      instr_reads_qlr = instr_reads_rs2_i;
    end else if (instr_rd_i == AssignedTag) begin
      instr_reads_qlr = instr_reads_rd_i;
    end
  end

  // ----------------
  // RF REQUEST
  // ----------------
  always_comb begin
    // Default
    rf_fsm_state_d = rf_fsm_state_q;
    rf_fsm_cntr_d  = rf_fsm_cntr_q;

    // Data passthrough from FIFO
    rf_out_data_o = fifo_out;

    // Default RF request
    rf_out_req_o = 1'b0;
    rf_out_tag_o = AssignedTag;

    // Default scoreboard
    qlr_sb_enabled_o = 1'b0;
    qlr_sb_o         = 1'b0;

    // FSM
    unique case (rf_fsm_state_q)
      // RFIdle state resets RF read counter and waits for the start signal
      RFIdle: begin
        rf_fsm_cntr_d = 1;
        // On incoming QLR start transition to UpdateRF
        if (iqlr_start == 1'b1) begin
          rf_fsm_state_d = UpdateRF;
        end
      end

      // UpdateRF state requests an RF write to update the register and
      // provides a dirty bit to the scoreboard output
      UpdateRF: begin
        // RF write request
        // (for in/out QLRs stall request if FIFO pop stall has not
        // been resolved yet to avoid writing the same data again)
        rf_out_req_o     = ~fifo_empty & ~fifo_iqlr_pop_stall_q;
        // Provide dirty bit to scoreboard
        qlr_sb_enabled_o = 1'b1;
        qlr_sb_o         = 1'b1;
        // RF write request granted
        if (rf_out_gnt_i == 1'b1) begin
          rf_fsm_state_d = SnoopInstr;
        end
        // If all LSU requests are done, transition to RFIdle once empty
        // (should only occur if user missconfigured QLR with 0 requests)
        if (req_fsm_state_q == ReqIdle) begin
          if (fifo_empty) begin
            rf_fsm_state_d = RFIdle;
          end
        end
      end

      // SnoopInstr state counts the number of RF reads and transitions
      // to UpdateRF once the configured amount has been reached, also
      // provides a clean bit to the scoreboard output
      SnoopInstr: begin
        // Provide clean bit to scoreboard
        qlr_sb_enabled_o = 1'b1;
        qlr_sb_o         = 1'b0;
        // Transition to UpdateRF once the configured amount of RF reads occurred
        if (instr_reads_qlr & instr_executed_i) begin
          rf_fsm_cntr_d = rf_fsm_cntr_q + 1;
          if (rf_fsm_cntr_q == rf_cntr_max_q) begin
            rf_fsm_cntr_d  = 1;
            rf_fsm_state_d = UpdateRF;
          end
        end
        // If all LSU requests are done, transition to RFIdle once empty
        if (req_fsm_state_q == ReqIdle) begin
          if (fifo_empty == 1'b1) begin
            rf_fsm_state_d = RFIdle;
          end
        end
      end
      default:;
    endcase
  end

  // ----------------
  // STALL SIGNAL
  // ----------------
  // For outgoing QLRs stalling is necessary if FIFO is full
  // (stalling prevents further writes to assigned register)
  assign qlr_fifo_stall_o = oqlr_enabled_q ? fifo_full : 1'b0;

  // ----------------
  // SEQUENTIAL
  // ----------------
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      fifo_iqlr_pop_stall_q <= 1'b0;
      fifo_oqlr_pop_stall_q <= 1'b0;
      iqlr_enabled_q        <= 1'b0;
      oqlr_enabled_q        <= 1'b0;
      req_cntr_max_q        <= 0;
      rf_cntr_max_q         <= 1;
      iqlr_addr_q           <= 'b0;
      oqlr_addr_q           <= 'b0;
      req_fsm_state_q       <= ReqIdle;
      req_fsm_cntr_q        <= 0;
      rf_fsm_state_q        <= RFIdle;
      rf_fsm_cntr_q         <= 1;
    end else begin
      fifo_iqlr_pop_stall_q <= fifo_iqlr_pop_stall_d;
      fifo_oqlr_pop_stall_q <= fifo_oqlr_pop_stall_d;
      iqlr_enabled_q        <= iqlr_enabled_d;
      oqlr_enabled_q        <= oqlr_enabled_d;
      req_cntr_max_q        <= req_cntr_max_d;
      rf_cntr_max_q         <= rf_cntr_max_d;
      iqlr_addr_q           <= iqlr_addr_d;
      oqlr_addr_q           <= oqlr_addr_d;
      req_fsm_state_q       <= req_fsm_state_d;
      req_fsm_cntr_q        <= req_fsm_cntr_d;
      rf_fsm_state_q        <= rf_fsm_state_d;
      rf_fsm_cntr_q         <= rf_fsm_cntr_d;
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
  if (NumWritePorts == 0) begin
    $error($sformatf("Module does not support NumWritePorts = 0."));
  end
  if (FifoSize == 0) begin
    $error($sformatf("Module does not support FifoSize = 0."));
  end
  if (MaxRequests == 0) begin
    $error($sformatf("Module does not support MaxRequests = 0."));
  end
  if (MaxRfReads == 0) begin
    $error($sformatf("Module does not support MaxRfReads = 0."));
  end

  `ifndef VERILATOR
    fifo_pop_stall_iqlr : assert property(
      @(posedge clk_i) disable iff (~rst_ni) (!(fifo_iqlr_pop_stall_q & ~oqlr_enabled_q)))
      else $fatal (1, "FIFO pop stalled despite RF request granted (IQLR).");
  `endif

  `ifndef VERILATOR
    fifo_pop_stall_oqlr : assert property(
      @(posedge clk_i) disable iff (~rst_ni) (!(fifo_oqlr_pop_stall_q & ~iqlr_enabled_q)))
      else $fatal (1, "FIFO pop stalled despite QPush response received (OQLR).");
  `endif
  // pragma translate_on

endmodule
