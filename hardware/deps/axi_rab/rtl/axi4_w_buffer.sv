// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

module axi4_w_buffer
  #(
    parameter AXI_DATA_WIDTH   = 32,
    parameter AXI_ID_WIDTH     = 4,
    parameter AXI_USER_WIDTH   = 4,
    parameter ENABLE_L2TLB     = 0,
    parameter HUM_BUFFER_DEPTH = 16
  )
  (
    input  logic                        axi4_aclk,
    input  logic                        axi4_arstn,

    // L1 & L2 interfaces
    output logic                        l1_done_o,
    input  logic                        l1_accept_i,
    input  logic                        l1_save_i,
    input  logic                        l1_drop_i,
    input  logic                        l1_master_i,
    input  logic     [AXI_ID_WIDTH-1:0] l1_id_i,
    input  logic                  [7:0] l1_len_i,
    input  logic                        l1_prefetch_i,
    input  logic                        l1_hit_i,

    output logic                        l2_done_o,
    input  logic                        l2_accept_i,
    input  logic                        l2_drop_i,
    input  logic                        l2_master_i,
    input  logic     [AXI_ID_WIDTH-1:0] l2_id_i,
    input  logic                  [7:0] l2_len_i,
    input  logic                        l2_prefetch_i,
    input  logic                        l2_hit_i,

    output logic                        master_select_o,
    output logic                        input_stall_o,
    output logic                        output_stall_o,

    // B sender interface
    output logic                        b_drop_o,
    input  logic                        b_done_i,
    output logic     [AXI_ID_WIDTH-1:0] id_o,
    output logic                        prefetch_o,
    output logic                        hit_o,

    // AXI W channel interfaces
    input  logic   [AXI_DATA_WIDTH-1:0] s_axi4_wdata,
    input  logic                        s_axi4_wvalid,
    output logic                        s_axi4_wready,
    input  logic [AXI_DATA_WIDTH/8-1:0] s_axi4_wstrb,
    input  logic                        s_axi4_wlast,
    input  logic   [AXI_USER_WIDTH-1:0] s_axi4_wuser,

    output logic   [AXI_DATA_WIDTH-1:0] m_axi4_wdata,
    output logic                        m_axi4_wvalid,
    input  logic                        m_axi4_wready,
    output logic [AXI_DATA_WIDTH/8-1:0] m_axi4_wstrb,
    output logic                        m_axi4_wlast,
    output logic   [AXI_USER_WIDTH-1:0] m_axi4_wuser
  );

  localparam BUFFER_WIDTH  = AXI_DATA_WIDTH+AXI_USER_WIDTH+AXI_DATA_WIDTH/8+1;

  localparam INPUT_BUFFER_DEPTH = 4;
  localparam L1_FIFO_DEPTH      = 8;
  localparam L2_FIFO_DEPTH      = 4;

  logic                             l1_req;
  logic                             l1_save_in, l1_save_out;
  logic [$clog2(L1_FIFO_DEPTH)-1:0] n_l1_save_SP;


  logic                           l2_req;

  logic                           fifo_select, fifo_select_SN, fifo_select_SP;
  logic                           w_done;
  logic                           b_drop_set;

  // HUM buffer signals
  logic                           hum_buf_ready_out;
  logic                           hum_buf_valid_in;
  logic                           hum_buf_ready_in;
  logic                           hum_buf_valid_out;
  logic                           hum_buf_underfull;

  logic      [AXI_DATA_WIDTH-1:0] hum_buf_wdata;
  logic    [AXI_DATA_WIDTH/8-1:0] hum_buf_wstrb;
  logic                           hum_buf_wlast;
  logic      [AXI_USER_WIDTH-1:0] hum_buf_wuser;

  logic                           hum_buf_drop_req_SN, hum_buf_drop_req_SP;
  logic                     [7:0] hum_buf_drop_len_SN, hum_buf_drop_len_SP;
  logic                           hum_buf_almost_full;

  logic                           stop_store;
  logic                           wlast_in, wlast_out;
  logic signed              [3:0] n_wlast_SN,          n_wlast_SP;
  logic                           block_forwarding;

  // Search FSM
  typedef enum logic        [3:0] {STORE,                       BYPASS,
                                   WAIT_L1_BYPASS_YES,          WAIT_L2_BYPASS_YES,
                                   WAIT_L1_BYPASS_NO,           WAIT_L2_BYPASS_NO,
                                   FLUSH,                       DISCARD,
                                   DISCARD_FINISH}
                                  hum_buf_state_t;
  hum_buf_state_t                 hum_buf_SP; // Present state
  hum_buf_state_t                 hum_buf_SN; // Next State

  typedef struct packed {
    logic [AXI_DATA_WIDTH-1:0]    data;
    logic [AXI_DATA_WIDTH/8-1:0]  strb;
    logic [AXI_USER_WIDTH-1:0]    user;
    logic                         last;
  } axi_w_t;

  axi_w_t axi_w;
  logic   axi_w_valid, axi_w_ready;
  stream_fifo #(
    .FALL_THROUGH (1'b0),
    .DEPTH        (INPUT_BUFFER_DEPTH),
    .T            (axi_w_t)
  ) i_input_buf (
    .clk_i      (axi4_aclk),
    .rst_ni     (axi4_arstn),
    .flush_i    (1'b0),
    .testmode_i (1'b0),
    .data_i     ('{ data: s_axi4_wdata,
                    strb: s_axi4_wstrb,
                    user: s_axi4_wuser,
                    last: s_axi4_wlast}),
    .valid_i    (s_axi4_wvalid),
    .ready_o    (s_axi4_wready),
    .data_o     (axi_w),
    .valid_o    (axi_w_valid),
    .ready_i    (axi_w_ready),
    .usage_o    (/* unused */)
  );

  typedef struct packed {
    logic                     prefetch;
    logic                     hit;
    logic [AXI_ID_WIDTH-1:0]  id;
    axi_pkg::len_t            len;
    logic                     master;
    logic                     accept;
    logic                     save;
    logic                     drop;
  } desc_t;

  desc_t l1;
  logic l1_fifo_inp_valid, l1_fifo_inp_ready,
        l1_fifo_oup_valid, l1_fifo_oup_ready;
  stream_fifo #(
    .FALL_THROUGH (1'b0),
    .DEPTH        (L1_FIFO_DEPTH),
    .T            (desc_t)
  ) i_l1_fifo (
    .clk_i  (axi4_aclk),
    .rst_ni (axi4_arstn),
    .flush_i    (1'b0),
    .testmode_i (1'b0),
    .data_i     ('{ prefetch: l1_prefetch_i,
                    hit:      l1_hit_i,
                    id:       l1_id_i,
                    len:      l1_len_i,
                    master:   l1_master_i,
                    accept:   l1_accept_i,
                    save:     l1_save_i,
                    drop:     l1_drop_i}),
    .valid_i    (l1_fifo_inp_valid),
    .ready_o    (l1_fifo_inp_ready),
    .data_o     (l1),
    .valid_o    (l1_fifo_oup_valid),
    .ready_i    (l1_fifo_oup_ready),
    .usage_o    (/* unused */)
  );

  desc_t l2;
  logic l2_fifo_inp_valid, l2_fifo_inp_ready,
        l2_fifo_oup_valid, l2_fifo_oup_ready;

    // Push upon receiving new requests from the TLB.
    assign l1_req           = l1_accept_i | l1_save_i | l1_drop_i;
    assign l1_fifo_inp_valid = l1_req & l1_fifo_inp_ready;

    // Signal handshake
    assign l1_done_o  = l1_fifo_inp_valid;
    assign l2_done_o  = l2_fifo_inp_valid;

    // Stall AW input of L1 TLB
    assign input_stall_o = ~(l1_fifo_inp_ready & l2_fifo_inp_ready);

    // Interface b_drop signals + handshake
    always_comb begin
      if (fifo_select == 1'b0) begin
        prefetch_o       = l1.prefetch;
        hit_o            = l1.hit;
        id_o             = l1.id;

        l1_fifo_oup_ready = w_done | b_done_i;
        l2_fifo_oup_ready = 1'b0;
      end else begin
        prefetch_o       = l2.prefetch;
        hit_o            = l2.hit;
        id_o             = l2.id;

        l1_fifo_oup_ready = 1'b0;
        l2_fifo_oup_ready = w_done | b_done_i;
      end
    end

    // Detect when an L1 transaction save request enters or exits the L1 FIFO.
    assign l1_save_in  = l1_fifo_inp_valid & l1_save_i;
    assign l1_save_out = l1_fifo_oup_ready & l1.save;

    // Count the number of L1 transaction to save in the L1 FIFO.
    always_ff @(posedge axi4_aclk or negedge axi4_arstn) begin
      if (axi4_arstn == 0) begin
        n_l1_save_SP <= '0;
      end else if (l1_save_in ^ l1_save_out) begin
        if (l1_save_in) begin
          n_l1_save_SP <= n_l1_save_SP + 1'b1;
        end else if (l1_save_out) begin
          n_l1_save_SP <= n_l1_save_SP - 1'b1;
        end
      end
    end

    // Stall forwarding of AW L1 hits if:
    // 1. The HUM buffer does not allow to be bypassed.
    // 2. There are multiple L1 save requests in the FIFO, i.e., multiple L2 outputs pending.
    assign output_stall_o = (n_l1_save_SP > 1) || (block_forwarding == 1'b1);

  generate
  if (ENABLE_L2TLB == 1) begin : HUM_BUFFER

    axi_buffer_rab_bram
    #(
      .DATA_WIDTH       ( BUFFER_WIDTH      ),
      .BUFFER_DEPTH     ( HUM_BUFFER_DEPTH  )
      )
    u_hum_buf
    (
      .clk           ( axi4_aclk                                                    ),
      .rstn          ( axi4_arstn                                                   ),
      // Push
      .data_in       ( {axi_w.user,    axi_w.strb,    axi_w.data,    axi_w.last}    ),
      .valid_in      ( hum_buf_valid_in                                             ),
      .ready_out     ( hum_buf_ready_out                                            ),
      // Pop
      .data_out      ( {hum_buf_wuser, hum_buf_wstrb, hum_buf_wdata, hum_buf_wlast} ),
      .valid_out     ( hum_buf_valid_out                                            ),
      .ready_in      ( hum_buf_ready_in                                             ),
      // Clear
      .almost_full   ( hum_buf_almost_full                                          ),
      .underfull     ( hum_buf_underfull                                            ),
      .drop_req      ( hum_buf_drop_req_SP                                          ),
      .drop_len      ( hum_buf_drop_len_SP                                          )
    );

    stream_fifo #(
      .FALL_THROUGH (1'b0),
      .DEPTH        (L2_FIFO_DEPTH),
      .T            (desc_t)
    ) i_l2_fifo (
      .clk_i  (axi4_aclk),
      .rst_ni (axi4_arstn),
      .flush_i    (1'b0),
      .testmode_i (1'b0),
      .data_i     ('{ prefetch: l2_prefetch_i,
                      hit:      l2_hit_i,
                      id:       l2_id_i,
                      len:      l2_len_i,
                      master:   l2_master_i,
                      accept:   l2_accept_i,
                      save:     1'bx, /* unused in L2 */
                      drop:     l2_drop_i}),
      .valid_i    (l2_fifo_inp_valid),
      .ready_o    (l2_fifo_inp_ready),
      .data_o     (l2),
      .valid_o    (l2_fifo_oup_valid),
      .ready_i    (l2_fifo_oup_ready),
      .usage_o    (/* unused */)
    );

    // Push upon receiving new result from TLB.
    assign l2_req           = l2_accept_i | l2_drop_i;
    assign l2_fifo_inp_valid = l2_req & l2_fifo_inp_ready;

    assign wlast_in  =    axi_w.last & hum_buf_valid_in  & hum_buf_ready_out;
    assign wlast_out = hum_buf_wlast & hum_buf_valid_out & hum_buf_ready_in;

    always_ff @(posedge axi4_aclk or negedge axi4_arstn) begin
      if (axi4_arstn == 0) begin
        fifo_select_SP      <= 1'b0;
        hum_buf_drop_len_SP <=  'b0;
        hum_buf_drop_req_SP <= 1'b0;
        hum_buf_SP          <= STORE;
        n_wlast_SP          <=  'b0;
      end else begin
        fifo_select_SP      <= fifo_select_SN;
        hum_buf_drop_len_SP <= hum_buf_drop_len_SN;
        hum_buf_drop_req_SP <= hum_buf_drop_req_SN;
        hum_buf_SP          <= hum_buf_SN;
        n_wlast_SP          <= n_wlast_SN;
      end
    end

    always_comb begin
      n_wlast_SN = n_wlast_SP;
      if (hum_buf_drop_req_SP) begin  // Happens exactly once per burst to be dropped.
        n_wlast_SN -= 1;
      end
      if (wlast_in) begin
        n_wlast_SN += 1;
      end
      if (wlast_out) begin
        n_wlast_SN -= 1;
      end
    end

    always_comb begin : HUM_BUFFER_FSM
      hum_buf_SN       = hum_buf_SP;

      m_axi4_wlast     = 1'b0;
      m_axi4_wdata     =  'b0;
      m_axi4_wstrb     =  'b0;
      m_axi4_wuser     =  'b0;

      m_axi4_wvalid    = 1'b0;
      axi_w_ready      = 1'b0;

      hum_buf_valid_in = 1'b0;
      hum_buf_ready_in = 1'b0;

      hum_buf_drop_req_SN = hum_buf_drop_req_SP;
      hum_buf_drop_len_SN = hum_buf_drop_len_SP;
      master_select_o  = 1'b0;

      w_done           = 1'b0; // read from FIFO without handshake with B sender
      b_drop_o         = 1'b0; // send data from FIFO to B sender (with handshake)
      fifo_select      = 1'b0;

      fifo_select_SN   = fifo_select_SP;
      stop_store       = 1'b0;

      block_forwarding = 1'b0;

      unique case (hum_buf_SP)

        STORE : begin
          // Simply store the data in the buffer.
          hum_buf_valid_in = axi_w_valid & hum_buf_ready_out;
          axi_w_ready      = hum_buf_ready_out;

          // We have got a full burst in the HUM buffer, thus stop storing.
          if (wlast_in & !hum_buf_underfull | (n_wlast_SP > $signed(0))) begin
            hum_buf_SN = WAIT_L1_BYPASS_YES;

          // The buffer is full, thus wait for decision.
          end else if (~hum_buf_ready_out) begin
            hum_buf_SN = WAIT_L1_BYPASS_NO;
          end

          // Avoid the forwarding of L1 hits until we know whether we can bypass.
          if (l1_fifo_oup_valid & l1.save) begin
            block_forwarding = 1'b1;
          end
        end

        WAIT_L1_BYPASS_YES : begin
          // Wait for orders from L1 TLB.
          if (l1_fifo_oup_valid) begin

            // L1 hit - forward data from buffer
            if (l1.accept) begin
              m_axi4_wlast       = hum_buf_wlast;
              m_axi4_wdata       = hum_buf_wdata;
              m_axi4_wstrb       = hum_buf_wstrb;
              m_axi4_wuser       = hum_buf_wuser;

              m_axi4_wvalid      = hum_buf_valid_out;
              hum_buf_ready_in   = m_axi4_wready;

              master_select_o    = l1.master;

              // Detect last data beat.
              if (wlast_out) begin
                fifo_select      = 1'b0;
                w_done           = 1'b1;
                hum_buf_SN       = STORE;
              end

            // L1 miss - wait for L2
            end else if (l1.save) begin
              fifo_select        = 1'b0;
              w_done             = 1'b1;
              hum_buf_SN         = WAIT_L2_BYPASS_YES;

            // L1 prefetch, prot, multi - drop data
            end else if (l1.drop) begin
              fifo_select_SN      = 1'b0; // L1
              hum_buf_drop_req_SN = 1'b1;
              hum_buf_drop_len_SN = l1.len;
              hum_buf_SN          = FLUSH;
            end
          end
        end

        WAIT_L2_BYPASS_YES : begin
          // Wait for orders from L2 TLB.
          if (l2_fifo_oup_valid) begin

            // L2 hit - forward data from buffer
            if (l2.accept) begin
              m_axi4_wlast       = hum_buf_wlast;
              m_axi4_wdata       = hum_buf_wdata;
              m_axi4_wstrb       = hum_buf_wstrb;
              m_axi4_wuser       = hum_buf_wuser;

              m_axi4_wvalid      = hum_buf_valid_out;
              hum_buf_ready_in   = m_axi4_wready;

              master_select_o    = l2.master;

              // Detect last data beat.
              if (wlast_out) begin
                fifo_select      = 1'b1;
                w_done           = 1'b1;
                hum_buf_SN       = STORE;
              end

            // L2 miss/prefetch hit
            end else if (l2.drop) begin
              fifo_select_SN      = 1'b1; // L2
              hum_buf_drop_req_SN = 1'b1;
              hum_buf_drop_len_SN = l2.len;
              hum_buf_SN          = FLUSH;
            end

          // While we wait for orders from L2 TLB, we can still drop and accept L1 transactions.
          end else if (l1_fifo_oup_valid) begin

            // L1 hit
            if (l1.accept) begin
              hum_buf_SN         = BYPASS;

            // L1 prefetch/prot/multi
            end else if (l1.drop) begin
              hum_buf_SN         = DISCARD;
            end
          end
        end

        FLUSH : begin
          // Clear HUM buffer flush request.
          hum_buf_drop_req_SN = 1'b0;

          // perform handshake with B sender
          fifo_select      = fifo_select_SP;
          b_drop_o         = 1'b1;
          if (b_done_i) begin
            hum_buf_SN     = STORE;
          end
        end

        BYPASS : begin
          // Forward one full transaction from input buffer.
          m_axi4_wlast       = axi_w.last;
          m_axi4_wdata       = axi_w.data;
          m_axi4_wstrb       = axi_w.strb;
          m_axi4_wuser       = axi_w.user;

          m_axi4_wvalid      = axi_w_valid;
          axi_w_ready        = m_axi4_wready;

          master_select_o    = l1.master;

          // We have got a full transaction.
          if (axi_w.last & axi_w_ready & axi_w_valid) begin
            fifo_select      = 1'b0;
            w_done           = 1'b1;
            hum_buf_SN       = WAIT_L2_BYPASS_YES;
          end
        end

        DISCARD : begin
          // Discard one full transaction from input buffer.
          axi_w_ready        = 1'b1;

          // We have got a full transaction.
          if (axi_w.last & axi_w_ready & axi_w_valid) begin
            // Try to perform handshake with B sender.
            fifo_select      = 1'b0;
            b_drop_o         = 1'b1;
            // We cannot wait here due to axi_w_ready.
            if (b_done_i) begin
              hum_buf_SN     = WAIT_L2_BYPASS_YES;
            end else begin
              hum_buf_SN     = DISCARD_FINISH;
            end
          end
        end

        DISCARD_FINISH : begin
          // Perform handshake with B sender.
          fifo_select      = 1'b0;
          b_drop_o         = 1'b1;
          if (b_done_i) begin
            hum_buf_SN     = WAIT_L2_BYPASS_YES;
          end
        end

        WAIT_L1_BYPASS_NO : begin
          // Do not allow the forwarding of L1 hits.
          block_forwarding       = 1'b1;

          // Wait for orders from L1 TLB.
          if (l1_fifo_oup_valid) begin

            // L1 hit - forward data from/through HUM buffer and refill the buffer
            if (l1.accept) begin
              // Forward data from HUM buffer.
              m_axi4_wlast       = hum_buf_wlast;
              m_axi4_wdata       = hum_buf_wdata;
              m_axi4_wstrb       = hum_buf_wstrb;
              m_axi4_wuser       = hum_buf_wuser;

              m_axi4_wvalid      = hum_buf_valid_out;
              hum_buf_ready_in   = m_axi4_wready;

              master_select_o    = l1.master;

              // Refill the HUM buffer. Stop when buffer full.
              stop_store         = ~hum_buf_ready_out;
              hum_buf_valid_in   = stop_store ? 1'b0 : axi_w_valid      ;
              axi_w_ready        = stop_store ? 1'b0 : hum_buf_ready_out;

              // Detect last data beat.
              if (wlast_out) begin
                fifo_select      = 1'b0;
                w_done           = 1'b1;
                if (~hum_buf_ready_out | hum_buf_almost_full) begin
                  hum_buf_SN     = WAIT_L1_BYPASS_NO;
                end else begin
                  hum_buf_SN     = STORE;
                end
              end

              // Allow the forwarding of L1 hits.
              block_forwarding   = 1'b0;

            // L1 miss - wait for L2
            end else if (l1.save) begin
              fifo_select        = 1'b0;
              w_done             = 1'b1;
              hum_buf_SN         = WAIT_L2_BYPASS_NO;

            // L1 prefetch, prot, multi - drop data
            end else if (l1.drop) begin
              fifo_select_SN      = 1'b0; // L1
              hum_buf_drop_req_SN = 1'b1;
              hum_buf_drop_len_SN = l1.len;
              hum_buf_SN          = FLUSH;

              // Allow the forwarding of L1 hits.
              block_forwarding   = 1'b0;
            end
          end
        end

        WAIT_L2_BYPASS_NO : begin
          // Do not allow the forwarding of L1 hits.
          block_forwarding       = 1'b1;

          // Wait for orders from L2 TLB.
          if (l2_fifo_oup_valid) begin

            // L2 hit - forward first part from HUM buffer, rest from input buffer
            if (l2.accept) begin
              // Forward data from HUM buffer.
              m_axi4_wlast       = hum_buf_wlast;
              m_axi4_wdata       = hum_buf_wdata;
              m_axi4_wstrb       = hum_buf_wstrb;
              m_axi4_wuser       = hum_buf_wuser;

              m_axi4_wvalid      = hum_buf_valid_out;
              hum_buf_ready_in   = m_axi4_wready;

              master_select_o    = l2.master;

              // Refill the HUM buffer. Stop when buffer full.
              stop_store         = ~hum_buf_ready_out;
              hum_buf_valid_in   = stop_store ? 1'b0 : axi_w_valid      ;
              axi_w_ready        = stop_store ? 1'b0 : hum_buf_ready_out;

              // Detect last data beat.
              if (wlast_out) begin
                fifo_select      = 1'b1;
                w_done           = 1'b1;
                if (~hum_buf_ready_out | hum_buf_almost_full) begin
                  hum_buf_SN     = WAIT_L1_BYPASS_NO;
                end else begin
                  hum_buf_SN     = STORE;
                end
              end

              // Allow the forwarding of L1 hits.
              block_forwarding   = 1'b0;

            // L2 miss/prefetch hit - drop data
            end else if (l2.drop) begin
              fifo_select_SN      = 1'b1; // L2
              hum_buf_drop_req_SN = 1'b1;
              hum_buf_drop_len_SN = l2.len;
              hum_buf_SN          = FLUSH;

              // Allow the forwarding of L1 hits.
              block_forwarding   = 1'b0;
            end
          end
        end


        default: begin
          hum_buf_SN = STORE;
        end

      endcase // hum_buf_SP
    end // HUM_BUFFER_FSM

    assign b_drop_set = 1'b0;

  end else begin // HUM_BUFFER

    // register to perform the handshake with B sender
    always_ff @(posedge axi4_aclk or negedge axi4_arstn) begin
      if (axi4_arstn == 0) begin
        b_drop_o <= 1'b0;
      end else if (b_done_i) begin
        b_drop_o <= 1'b0;
      end else if (b_drop_set) begin
        b_drop_o <= 1'b1;;
      end
    end

    always_comb begin : OUTPUT_CTRL

      fifo_select   = 1'b0;
      w_done        = 1'b0;
      b_drop_set    = 1'b0;

      m_axi4_wlast  = 1'b0;
      m_axi4_wdata  =  'b0;
      m_axi4_wstrb  =  'b0;
      m_axi4_wuser  =  'b0;

      m_axi4_wvalid = 1'b0;
      axi_w_ready   = 1'b0;

      if (l1_fifo_oup_valid) begin
        // forward data
        if (l1.accept) begin
          m_axi4_wlast  = axi_w.last;
          m_axi4_wdata  = axi_w.data;
          m_axi4_wstrb  = axi_w.strb;
          m_axi4_wuser  = axi_w.user;

          m_axi4_wvalid = axi_w_valid;
          axi_w_ready   = m_axi4_wready;

          // Simply pop from FIFO upon last data beat.
          w_done        = axi_w.last & axi_w_valid & axi_w_ready;

        // discard entire burst
        end else if (b_drop_o == 1'b0) begin
          axi_w_ready   = 1'b1;

          // Simply pop from FIFO upon last data beat. Perform handshake with B sender.
          if (axi_w.last & axi_w_valid & axi_w_ready)
            b_drop_set  = 1'b1;
        end
      end

    end // OUTPUT_CTRL

    assign master_select_o     = l1.master;
    assign l2_fifo_inp_ready   = 1'b1;
    assign block_forwarding    = 1'b0;

    // unused signals
    assign hum_buf_ready_out   = 1'b0;
    assign hum_buf_valid_in    = 1'b0;
    assign hum_buf_ready_in    = 1'b0;
    assign hum_buf_valid_out   = 1'b0;
    assign hum_buf_wdata       =  'b0;
    assign hum_buf_wstrb       =  'b0;
    assign hum_buf_wlast       = 1'b0;
    assign hum_buf_wuser       =  'b0;
    assign hum_buf_drop_len_SN =  'b0;
    assign hum_buf_drop_req_SN = 1'b0;
    assign hum_buf_almost_full = 1'b0;

    assign l2                  = '{default: '0};
    assign l2_fifo_inp_valid   = 1'b0;
    assign l2_fifo_oup_valid   = 1'b0;

    assign l2_req              = 1'b0;

    assign fifo_select_SN      = 1'b0;
    assign fifo_select_SP      = 1'b0;

    assign stop_store          = 1'b0;
    assign n_wlast_SP          =  'b0;
    assign wlast_in            = 1'b0;
    assign wlast_out           = 1'b0;

  end // HUM_BUFFER

  endgenerate

endmodule
