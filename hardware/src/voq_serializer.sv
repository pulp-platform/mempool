// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Virtual output queues with a serializer per output. A wide transaction of NumBeats beats,
// for one of NumOut outputs, is accepted in one cycle into a shared buffer of NumEntries
// transactions and sent to its output one beat per cycle, so transactions for different outputs
// are sent concurrently. Per output: an index queue keeps the arrival order, a prefetch register
// is filled from the shared buffer (one read per cycle, round robin over the outputs) while the
// head register sends; a transaction with nothing in front of it cuts through. Beats leave in
// the order LastBeat+1, ..., NumBeats-1, 0, ..., LastBeat. Order is kept per output only.
// A buffer entry is freed when its transaction is read into the prefetch register; a
// cut-through takes none. Options: a cap per output (OutCap); reservations (NumRsv producers,
// at most two, reserve a place before the data comes, the input handshake then commits it and
// must find the place; every reservation holds a buffer credit, so a commit always finds an
// entry; rsv_ready_o comes from a register).

`include "common_cells/assertions.svh"
`include "common_cells/registers.svh"

module voq_serializer #(
  // Transactions held in the shared buffer
  parameter int unsigned NumEntries    = 16,
  parameter int unsigned NumBeats      = 8,
  parameter int unsigned NumOut        = 4,
  // Beat sent last
  parameter int unsigned LastBeat      = NumBeats - 1,
  parameter type         beat_t        = logic,
  // Data of a transaction sent with each of its beats
  parameter type         meta_t        = logic,
  // Transactions per output, reserved or held (0: no cap)
  parameter int unsigned OutCap        = 0,
  // Producers that reserve (0: no reservations)
  parameter int unsigned NumRsv        = 0,
  // Read the shared buffer only into an empty prefetch register
  parameter bit          PrefetchEmpty = 1'b0,
  // Dependent parameters, do not override
  parameter int unsigned OutIdxW       = (NumOut > 1) ? $clog2(NumOut) : 1,
  parameter int unsigned BeatIdxW      = (NumBeats > 1) ? $clog2(NumBeats) : 1,
  parameter int unsigned RsvW          = (NumRsv > 0) ? NumRsv : 1
) (
  input  logic                                 clk_i,
  input  logic                                 rst_ni,
  input  beat_t [NumBeats-1:0]                 in_data_i,
  input  meta_t                                in_meta_i,
  input  logic  [OutIdxW-1:0]                  in_out_i,
  input  logic                                 in_valid_i,
  output logic                                 in_ready_o,
  // Output o would take a transaction now
  output logic  [NumOut-1:0]                   out_space_o,
  output beat_t [NumOut-1:0]                   out_data_o,
  output meta_t [NumOut-1:0]                   out_meta_o,
  output logic  [NumOut-1:0][BeatIdxW-1:0]     out_beat_o,
  output logic  [NumOut-1:0]                   out_last_o,
  output logic  [NumOut-1:0]                   out_valid_o,
  input  logic  [NumOut-1:0]                   out_ready_i,
  // Reservations: producer r reserves a place of output rsv_out_i[r]
  input  logic  [RsvW-1:0]                     rsv_valid_i,
  input  logic  [RsvW-1:0][OutIdxW-1:0]        rsv_out_i,
  output logic  [RsvW-1:0][NumOut-1:0]         rsv_ready_o,
  // Nothing buffered, being sent or reserved
  output logic                                 idle_o
);

  localparam int unsigned EntryW    = (NumEntries > 1) ? $clog2(NumEntries) : 1;
  localparam int unsigned BeatW     = BeatIdxW;
  localparam int unsigned FirstBeat = (LastBeat + 1) % NumBeats;
  localparam int unsigned CntW      = (OutCap > 0) ? $clog2(OutCap + 1) : 1;
  localparam int unsigned QDepth    = ((OutCap > 0) && (OutCap < NumEntries)) ? OutCap : NumEntries;
  localparam int unsigned CredW     = $clog2(NumEntries + 2) + 1;
  localparam int unsigned RsvCntW   = $clog2(RsvW + 1);  // reservations per cycle, at most one per producer
  localparam int unsigned TokW      = (RsvW > 1) ? $clog2(RsvW) : 1;

  // One transaction: its meta data above its beats
  typedef logic [$bits(meta_t) + NumBeats * $bits(beat_t) - 1:0] trans_t;

  trans_t in_trans;
  logic   in_hs;

  assign in_trans = {in_meta_i, in_data_i};
  assign in_hs    = in_valid_i && in_ready_o;

  /*******************
   *  Shared buffer  *
   *******************/

  trans_t [NumEntries-1:0] buf_q, buf_d;
  logic   [NumEntries-1:0] used_q, used_d;
  logic   [EntryW-1:0]     free_idx;
  logic                    free_ok, alloc;
  logic   [CredW-1:0]      buf_used;

  /*****************
   *  Serializers  *
   *****************/

  logic   [NumOut-1:0]             read_req, read_gnt, done, queue_empty, cut_ok, push;
  logic   [NumOut-1:0]             head_valid, pref_valid, commits;
  logic   [NumOut-1:0][EntryW-1:0] queue_idx;
  logic   [NumOut-1:0][CntW-1:0]   n_q, n_nx;
  logic   [OutIdxW-1:0]            read_out;
  trans_t                          read_data;

  for (genvar o = 0; o < NumOut; o++) begin : gen_out
    trans_t               head_q, head_d, pref_q, pref_d;
    beat_t [NumBeats-1:0] head_data;
    meta_t                head_meta;
    logic              head_valid_q, head_valid_d, pref_valid_q, pref_valid_d, queue_full;
    logic [BeatW-1:0]  cnt_q, cnt_d, beat;
    logic [BeatW:0]    beat_sum;
    logic              mine, cut, cut_to_head, to_pref, head_free, pref_free, advance, out_hs;

    // Input: cut through to a free register when nothing is queued, else queue
    assign mine        = in_hs && (in_out_i == OutIdxW'(o));
    assign commits[o]  = mine;
    assign cut_ok[o]   = queue_empty[o] && pref_free;
    assign cut         = mine && cut_ok[o];
    assign cut_to_head = cut && !pref_valid_q && head_free;
    assign to_pref     = cut && !cut_to_head;
    assign push[o]     = mine && !cut;

    // Index queue: buffer entries in arrival order
    fifo_v3 #(
      .FALL_THROUGH (1'b0              ),
      .DEPTH        (QDepth            ),
      .dtype        (logic [EntryW-1:0])
    ) i_queue (
      .clk_i      (clk_i          ),
      .rst_ni     (rst_ni         ),
      .flush_i    (1'b0           ),
      .testmode_i (1'b0           ),
      .full_o     (queue_full     ),
      .empty_o    (queue_empty[o] ),
      .usage_o    (/* unused */   ),
      .data_i     (free_idx       ),
      .push_i     (push[o]        ),
      .data_o     (queue_idx[o]   ),
      .pop_i      (read_gnt[o]    )
    );
    `ASSERT(voq_queue_no_overflow, push[o] |-> !queue_full, clk_i, !rst_ni,
            "Index queue of an output overflows")

    // Prefetch register: read from the buffer when free (or only when empty)
    assign pref_free   = !pref_valid_q || advance;
    assign read_req[o] = !queue_empty[o] && (PrefetchEmpty ? !pref_valid_q : pref_free);

    // Head register: takes the prefetched transaction when free
    assign head_free   = !head_valid_q || done[o];
    assign advance     = pref_valid_q && head_free;

    // Send, one beat per cycle
    assign beat_sum       = cnt_q + (BeatW+1)'(FirstBeat);
    assign beat           = (beat_sum >= NumBeats) ? BeatW'(beat_sum - NumBeats) : BeatW'(beat_sum);
    assign {head_meta, head_data} = head_q;
    assign out_data_o[o]  = head_data[beat];
    assign out_meta_o[o]  = head_meta;
    assign out_beat_o[o]  = beat;
    assign out_last_o[o]  = (cnt_q == BeatW'(NumBeats - 1));
    assign out_valid_o[o] = head_valid_q;
    assign out_hs         = head_valid_q && out_ready_i[o];
    assign done[o]        = out_hs && out_last_o[o];
    assign head_valid[o]  = head_valid_q;
    assign pref_valid[o]  = pref_valid_q;
    assign cnt_d          = !out_hs ? cnt_q : (out_last_o[o] ? '0 : cnt_q + 1'b1);

    assign pref_valid_d = read_gnt[o] || to_pref || (pref_valid_q && !advance);
    always_comb begin
      pref_d = pref_q;
      if (read_gnt[o]) begin
        pref_d = read_data;
      end else if (to_pref) begin
        pref_d = in_trans;
      end
    end

    assign head_valid_d = advance || cut_to_head || (head_valid_q && !done[o]);
    always_comb begin
      head_d = head_q;
      if (advance) begin
        head_d = pref_q;
      end else if (cut_to_head) begin
        head_d = in_trans;
      end
    end

    `FF(pref_valid_q, pref_valid_d, 1'b0, clk_i, rst_ni);
    `FF(head_valid_q, head_valid_d, 1'b0, clk_i, rst_ni);
    `FF(cnt_q,        cnt_d,        '0,   clk_i, rst_ni);
    `FFNR(pref_q, pref_d, clk_i);
    `FFNR(head_q, head_d, clk_i);
  end

  /*****************
   *  Input ready  *
   *****************/

  logic [NumOut-1:0] cap_ok;
  always_comb begin
    for (int o = 0; o < NumOut; o++) begin
      cap_ok[o]      = (NumRsv > 0) || (OutCap == 0) || (int'(n_q[o]) < OutCap);
      out_space_o[o] = (cut_ok[o] || free_ok) && cap_ok[o];
    end
  end
  assign in_ready_o = out_space_o[in_out_i];

  /*******************************
   *  Counts and reservations    *
   *******************************/

  logic [NumOut-1:0][RsvCntW-1:0] rsv_cnt; // How many reservations per direction in this cycle
  logic [CredW-1:0]               resv_q, resv_d; // How many reserved entries
  logic [TokW-1:0]                tok_q;

  always_comb begin
    for (int o = 0; o < NumOut; o++) begin
      rsv_cnt[o] = '0;
      for (int r = 0; r < NumRsv; r++) begin
        if (rsv_valid_i[r] && (rsv_out_i[r] == OutIdxW'(o))) rsv_cnt[o] = rsv_cnt[o] + 1'b1;
      end
    end
  end

  // Per direction: the count for the cap, and a check that each commit has a reservation
  for (genvar o = 0; o < NumOut; o++) begin : gen_count
    if (OutCap > 0) begin : gen_cap
      logic [CntW-1:0] n_d; // How many transactions in-flight (including reserved) but not yet sent
      assign n_d = n_q[o] + ((NumRsv > 0) ? CntW'(rsv_cnt[o]) : CntW'(commits[o])) - CntW'(done[o]);
      `FF(n_q[o], n_d, '0, clk_i, rst_ni);
      assign n_nx[o] = n_d;
      `ASSERT(voq_cap, int'(n_q[o]) <= OutCap, clk_i, !rst_ni,
              "An output holds more transactions than its cap")
    end else begin : gen_no_cap
      assign n_q[o]  = '0;
      assign n_nx[o] = '0;
    end
    if (NumRsv > 0) begin : gen_rsv_check
      logic [CntW-1:0] r_q, r_d;
      assign r_d = r_q + CntW'(rsv_cnt[o]) - CntW'(commits[o]);
      `FF(r_q, r_d, '0, clk_i, rst_ni);
      `ASSERT(voq_commit_reserved, int'(r_q) >= int'(commits[o]), clk_i, !rst_ni,
              "A commit for an output with no reservation in flight")
    end
  end

  if (NumRsv > 0) begin : gen_rsv
    logic [CredW-1:0]            credit, credit_nx; // How many entries are available to be reserved
    logic [RsvCntW-1:0]          rsv_all; // How many reservations have been requested this cycle
    logic [RsvW-1:0][NumOut-1:0] ready_q, ready_d, ready_rst;
    logic [TokW-1:0]             tok_d;  // Next cycle's token: who may take the last place (entry or room) if only one is left

    // Count how many reservations are requested this cycle
    always_comb begin
      rsv_all = '0;
      for (int o = 0; o < NumOut; o++) rsv_all = rsv_all + rsv_cnt[o];
    end
    assign resv_d = resv_q + CredW'(rsv_all) - CredW'(in_hs);
    assign credit = CredW'(NumEntries) - buf_used - resv_q;

    // Given the counts, the credit and the token, computes for each producer and direction whether it may reserve
    function automatic logic [RsvW-1:0][NumOut-1:0] ready_of(
        input logic [NumOut-1:0][CntW-1:0] n,
        input logic [CredW-1:0]            cred,
        input logic [TokW-1:0]             tok);
      logic [RsvW-1:0][NumOut-1:0] rdy;
      rdy = '0;
      for (int o = 0; o < NumOut; o++) begin
        automatic int unsigned room = (int'(n[o]) < OutCap) ? OutCap - int'(n[o]) : 0;
        for (int r = 0; r < NumRsv; r++) begin
          rdy[r][o] = ((room >= NumRsv) || ((room >= 1) && (int'(tok) == r))) &&
                      ((int'(cred) >= NumRsv) || ((int'(cred) >= 1) && (int'(tok) == r)));
        end
      end
      return rdy;
    endfunction

    // The ready from a register, computed from the next state
    assign credit_nx = CredW'(NumEntries) - CredW'($countones(used_d)) - resv_d;
    assign tok_d     = (NumRsv > 1) ? TokW'(tok_q + 1'b1) : '0;
    assign ready_d   = ready_of(n_nx, credit_nx, tok_d);
    assign ready_rst = ready_of('0, CredW'(NumEntries), '0);
    `FF(ready_q, ready_d, ready_rst, clk_i, rst_ni);
    assign rsv_ready_o = ready_q;
    `ASSERT(voq_ready_reg, ready_q == ready_of(n_q, credit, tok_q), clk_i, !rst_ni,
            "Registered reservation ready differs from the combinational one")

    if (NumRsv > 1) begin : gen_tok
      `FF(tok_q, tok_d, '0, clk_i, rst_ni);
    end else begin : gen_no_tok
      assign tok_q = '0;
    end
    `FF(resv_q, resv_d, '0, clk_i, rst_ni);

    for (genvar r = 0; r < NumRsv; r++) begin : gen_rsv_assert
      `ASSERT(voq_rsv_in_range, rsv_valid_i[r] |-> (rsv_out_i[r] < NumOut), clk_i, !rst_ni,
              "Reservation for an output that does not exist")
      `ASSERT(voq_rsv_ready, rsv_valid_i[r] |-> rsv_ready_o[r][rsv_out_i[r]], clk_i, !rst_ni,
              "Reservation without a place")
    end
    `ASSERT(voq_credit, (buf_used + resv_q) <= NumEntries, clk_i, !rst_ni,
            "Shared buffer overbooked")
    `ASSERT(voq_commit_place, in_valid_i |-> in_ready_o, clk_i, !rst_ni,
            "A reserved commit found no place")
  end else begin : gen_no_rsv
    assign rsv_ready_o = '0;
    assign resv_d      = '0;
    assign resv_q      = '0;
    assign tok_q       = '0;
  end

  /****************************
   *  Shared buffer storage   *
   ****************************/

  logic [OutIdxW-1:0] rr_q, rr_d;

  always_comb begin
    free_ok  = 1'b0;
    free_idx = '0;
    for (int i = NumEntries - 1; i >= 0; i--) begin
      if (!used_q[i]) begin
        free_ok  = 1'b1;
        free_idx = EntryW'(i);
      end
    end
  end

  // A cut-through takes no entry
  assign alloc    = |push;
  assign buf_used = CredW'($countones(used_q));

  // Shared buffer read port: round robin over the outputs
  always_comb begin
    read_gnt = '0;
    read_out = rr_q;
    for (int k = NumOut - 1; k >= 0; k--) begin
      automatic int unsigned o = (int'(rr_q) + k) % NumOut;
      if (read_req[o]) begin
        read_gnt    = '0;
        read_gnt[o] = 1'b1;
        read_out    = OutIdxW'(o);
      end
    end
    rr_d = (|read_gnt) ? ((read_out == OutIdxW'(NumOut - 1)) ? '0 : read_out + 1'b1) : rr_q;
  end

  assign read_data = buf_q[queue_idx[read_out]];

  // An entry is freed when it is read into the prefetch register
  always_comb begin
    used_d = used_q;
    for (int o = 0; o < NumOut; o++) begin
      if (read_gnt[o]) used_d[queue_idx[o]] = 1'b0;
    end
    if (alloc) used_d[free_idx] = 1'b1;
  end

  // Shared buffer write port
  always_comb begin
    buf_d = buf_q;
    if (alloc) buf_d[free_idx] = in_trans;
  end

  `FF(used_q, used_d, '0, clk_i, rst_ni);
  `FF(rr_q,   rr_d,   '0, clk_i, rst_ni);
  `FFNR(buf_q, buf_d, clk_i);

  `ASSERT(voq_write_free, alloc |-> free_ok, clk_i, !rst_ni,
          "Transaction written into a used buffer entry")

  assign idle_o = ~|used_q && ~|head_valid && ~|pref_valid && (resv_q == '0);

  `ASSERT_INIT(last_beat_in_range, LastBeat < NumBeats)
  `ASSERT(out_in_range, in_hs |-> (in_out_i < NumOut), clk_i, !rst_ni,
          "Transaction for an output that does not exist")

  if ((NumBeats < 1) || (NumOut < 1) || (NumEntries < 1))
    $error("[voq_serializer] NumBeats, NumOut and NumEntries must be at least 1");
  if (NumRsv > 2)
    $error("[voq_serializer] NumRsv must be at most 2");
  if ((NumRsv > 0) && (OutCap == 0))
    $error("[voq_serializer] reservations need OutCap");

endmodule : voq_serializer
