// Copyright 2022 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Samuel Riedel <sriedel@iis.ee.ethz.ch>
// Bowen Wang    <bowwang@student.ethz.ch>

// Mode selection: [1:0] dma_mode_i
// 2'b00: safe mode, no modificaion will be added to the transfer
// 2'b01: fast mode, only apply to L1-aligned address
// 2'b10: dupl mode, only apply to partition-aligned address
// 2'b11: NOP  

`include "common_cells/registers.svh"

module idma_distributed_midend_v2 #(
  /// Number of backends to distribute the requests to
  parameter int unsigned NoMstPorts     = 1,
  /// Bytes covered by each port
  parameter int unsigned DmaRegionWidth = 1, // [B] Region that one port covers in bytes
  /// Start of the distributed memory region
  parameter int unsigned DmaRegionStart = 32'h0000_0000,
  /// End of the distributed memory region
  parameter int unsigned DmaRegionEnd   = 32'h1000_0000,
  /// Number of generic 1D requests that can be buffered
  parameter int unsigned TransFifoDepth = 1,
  /// Arbitrary 1D burst request definition
  parameter type         burst_req_t    = logic,
  /// Meta data response definition
  parameter type         meta_t         = logic
) (
  input  logic                        clk_i,
  input  logic                        rst_ni,
  // Slave
  input  burst_req_t                  burst_req_i,
  input  logic                        valid_i,
  output logic                        ready_o,
  output meta_t                       meta_o,
  // partition related signals
  input  logic       [1:0]            dma_mode_i,
  input  logic       [7:0]            allocated_size_i, 
  // Master
  output burst_req_t [NoMstPorts-1:0] burst_req_o,
  output logic       [NoMstPorts-1:0] valid_o,
  input  logic       [NoMstPorts-1:0] ready_i,
  input  meta_t      [NoMstPorts-1:0] meta_i
);

  localparam DmaRegionAddressBits = $clog2(DmaRegionWidth);
  localparam FullRegionAddressBits = $clog2(DmaRegionWidth*NoMstPorts);
  localparam FullDmaRegionWidth = DmaRegionWidth*NoMstPorts;

  typedef logic [FullRegionAddressBits:0] full_addr_t;

  // Handle the ready signal
  logic fork_ready, fifo_ready;
  logic [NoMstPorts-1:0] fifo_full;
  // Handle Metadata
  logic [NoMstPorts-1:0] trans_complete_d, trans_complete_q;
  logic [NoMstPorts-1:0] tie_off_trans_complete_d, tie_off_trans_complete_q;
  logic [NoMstPorts-1:0] backend_idle_d, backend_idle_q;
  assign meta_o.trans_complete = &trans_complete_q;
  assign meta_o.backend_idle = &backend_idle_q;
  assign fifo_ready = !(|fifo_full);
  assign ready_o = fork_ready && fifo_ready;

  for (genvar i = 0; unsigned'(i) < NoMstPorts; i++) begin: gen_trans_complete_fifo
    // Collect the `trans_complete` signals and reduce them once we have all of them
    logic empty;
    logic data;
    logic conflict_push;
    fifo_v3 #(
      .FALL_THROUGH (0             ),
      .DATA_WIDTH   (1             ),
      .DEPTH        (TransFifoDepth)
    ) i_trans_complete_fifo (
      .clk_i      (clk_i                ),
      .rst_ni     (rst_ni               ),
      .flush_i    ('0                   ),
      .testmode_i ('0                   ),
      .full_o     (fifo_full[i]         ),
      .empty_o    (empty                ),
      .usage_o    (/*unused*/           ),
      .data_i     (1'b1                 ),
      .push_i     ( (trans_complete_d[i] |  conflict_push) & (fifo_full[i]==0) ),
      .data_o     (data                 ),
      .pop_i      (meta_o.trans_complete)
    );
    assign trans_complete_d[i] = meta_i[i].trans_complete | tie_off_trans_complete_q[i];
    assign trans_complete_q[i] = data && !empty;

    // handle two complete signals arrive at the same time
    logic [3:0] conflict_complete_d, conflict_complete_q;
    `FF(conflict_complete_q, conflict_complete_d, '0, clk_i, rst_ni)
    
    always_comb begin
      conflict_complete_d = conflict_complete_q;
      conflict_push = 0;
      if (meta_i[i].trans_complete & tie_off_trans_complete_q[i] & (fifo_full[i]==0)) begin // FIFO is not full
        conflict_complete_d = conflict_complete_q+1;
      end
      if (meta_i[i].trans_complete & tie_off_trans_complete_q[i] & (fifo_full[i]!=0)) begin // FIFO is full
        conflict_complete_d = conflict_complete_q+2;
      end
      if (!meta_i[i].trans_complete & tie_off_trans_complete_q[i] & (fifo_full[i]!=0)) begin
        conflict_complete_d = conflict_complete_q+1;
      end
      if (meta_i[i].trans_complete & !tie_off_trans_complete_q[i] & (fifo_full[i]!=0)) begin
        conflict_complete_d = conflict_complete_q+1;
      end

      if ( (conflict_complete_q!=0) & (trans_complete_d[i]==0) & (fifo_full[i]==0) ) begin // FIFO is not full, safe to push
        conflict_push = 1;
        conflict_complete_d = conflict_complete_q-1;
      end
    end

  end

  always_comb begin
    backend_idle_d = backend_idle_q;
    for (int unsigned i = 0; i < NoMstPorts; i++) begin
      backend_idle_d[i] = meta_i[i].backend_idle;
    end
  end
  `FF(tie_off_trans_complete_q, tie_off_trans_complete_d, '0, clk_i, rst_ni)
  `FF(backend_idle_q, backend_idle_d, '1, clk_i, rst_ni)

  // Fork
  logic [NoMstPorts-1:0] valid, ready;
  stream_fork #(
    .N_OUP (NoMstPorts)
  ) i_stream_fork (
    .clk_i   (clk_i               ),
    .rst_ni  (rst_ni              ),
    .valid_i (valid_i & fifo_ready),
    .ready_o (fork_ready          ),
    .valid_o (valid               ),
    .ready_i (ready               )
  );

  full_addr_t src_addr, dst_addr, start_addr, end_addr;

  assign src_addr = burst_req_i.src[FullRegionAddressBits-1:0];
  assign dst_addr = burst_req_i.dst[FullRegionAddressBits-1:0];

  logic [1:0] num_split, split_offset;
  // logic num_split, split_offset;

  always_comb begin
    num_split = burst_req_i.num_bytes / DmaRegionWidth;
    if (($unsigned(burst_req_i.src) >= DmaRegionStart) && ($unsigned(burst_req_i.src) < DmaRegionEnd)) begin
      start_addr = src_addr;
    end else begin
      start_addr = dst_addr;
    end
    end_addr = start_addr+burst_req_i.num_bytes;
    split_offset = start_addr[DmaRegionAddressBits+1:DmaRegionAddressBits];
    // split_offset = start_addr[DmaRegionAddressBits];
    // Connect valid ready by default
    valid_o = valid;
    ready = ready_i;
    // Do not interfere with metadata per default
    tie_off_trans_complete_d = '0;
    for (int i = 0; i < NoMstPorts; i++) begin
      tie_off_trans_complete_d[i] = tie_off_trans_complete_q[i] && meta_i[i].trans_complete;
      // Feed metadata through directly
      burst_req_o[i] = burst_req_i;
      // Feed through the address bits
      burst_req_o[i].src = burst_req_i.src;
      burst_req_o[i].dst = burst_req_i.dst;
      // Modify lower addresses bits and size
      if (($unsigned(start_addr) >= (i+1)*DmaRegionWidth) || ($unsigned(end_addr) <= i*DmaRegionWidth)) begin
        // We are not involved in the transfer
        if ( (dma_mode_i == 2'b00) || (dma_mode_i == 2'b11) ) begin // safe mode
          burst_req_o[i].src = '0;
          burst_req_o[i].dst = '0;
          burst_req_o[i].num_bytes = 1;
          // Make handshake ourselves
          valid_o[i] = 1'b0;
          ready[i] = 1'b1;
          // Inject trans complete
          if (valid[i]) begin
            tie_off_trans_complete_d[i] = 1'b1;
          end
        end else if (dma_mode_i == 2'b01) begin // fast mode
          burst_req_o[i].num_bytes = (burst_req_i.num_bytes<DmaRegionWidth) ? burst_req_i.num_bytes : DmaRegionWidth;
          if (($unsigned(burst_req_i.src) >= DmaRegionStart) && ($unsigned(burst_req_i.src) < DmaRegionEnd)) begin
            burst_req_o[i].src = burst_req_i.src+i*DmaRegionWidth;
            burst_req_o[i].dst = burst_req_i.dst+i*allocated_size_i*DmaRegionWidth;
          end else begin
            // L2 --> L1
            if (burst_req_i.num_bytes<=DmaRegionWidth )begin
              burst_req_o[i].src = burst_req_i.src+i*allocated_size_i*DmaRegionWidth;
            end else if (i==2) begin
              burst_req_o[i].src = burst_req_i.src+i*allocated_size_i*DmaRegionWidth;
            end else if (i==3) begin
              burst_req_o[i].src = burst_req_i.src+(i-1)*allocated_size_i*DmaRegionWidth + DmaRegionWidth;
            end
            burst_req_o[i].dst = burst_req_i.dst+i*DmaRegionWidth;
          end
        end else if (dma_mode_i == 2'b10) begin // duplication mode: only consider L2 --> L1
          if (($unsigned(burst_req_i.dst) >= DmaRegionStart) && ($unsigned(burst_req_i.dst) < DmaRegionEnd)) begin
            // L2 ------> L1
            burst_req_o[i].num_bytes = (burst_req_i.num_bytes<DmaRegionWidth) ? burst_req_i.num_bytes : DmaRegionWidth;
            // burst_req_o[i].src = burst_req_i.src+i*allocated_size_i*DmaRegionWidth;
            burst_req_o[i].src = (burst_req_i.num_bytes<=DmaRegionWidth) ? burst_req_i.src : burst_req_i.src+(i-2)*DmaRegionWidth;
            burst_req_o[i].dst = burst_req_i.dst+i*DmaRegionWidth;
          end 
        end

      end else if (($unsigned(start_addr) >= i*DmaRegionWidth)) begin
        // First (and potentially only) slice
        // Leave address as is
        if ($unsigned(end_addr) <= (i+1)*DmaRegionWidth) begin
          burst_req_o[i].num_bytes = burst_req_i.num_bytes;
        end else begin
          burst_req_o[i].num_bytes = DmaRegionWidth-start_addr[DmaRegionAddressBits-1:0];
        end
      // end else if (($unsigned(start_addr) < i*DmaRegionWidth)) begin

      end else begin
        // Round up the address to the next DMA boundary
        if (($unsigned(burst_req_i.src) >= DmaRegionStart) && ($unsigned(burst_req_i.src) < DmaRegionEnd)) begin
          burst_req_o[i].src[FullRegionAddressBits-1:0] = i*DmaRegionWidth;
          burst_req_o[i].dst = burst_req_i.dst+i*DmaRegionWidth-start_addr[DmaRegionAddressBits-1:0];
        end else begin
          burst_req_o[i].src = burst_req_i.src+(i-split_offset)*DmaRegionWidth-start_addr[DmaRegionAddressBits-1:0];
          burst_req_o[i].dst[FullRegionAddressBits-1:0] = i*DmaRegionWidth;
        end
        if ($unsigned(end_addr) >= (i+1)*DmaRegionWidth) begin
          // Middle slice
          // Emit a full-sized transfer
          burst_req_o[i].num_bytes = DmaRegionWidth;
        end else begin
          // Last slice
          burst_req_o[i].num_bytes = end_addr[DmaRegionAddressBits-1:0];
        end
      end
    end
  end

  // pragma translate_off
  int f;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    automatic string str;
    if (rst_ni && valid_i && ready_o) begin
      str = "\n[idma_distributed_midend_v2] Got request\n";
      str = $sformatf("%sRequest in: From: 0x%8x To: 0x%8x with size %d\n", str, burst_req_i.src, burst_req_i.dst, burst_req_i.num_bytes);
      for (int i = 0; i < NoMstPorts; i++) begin
        str = $sformatf("%sOut %6d: From: 0x%8x To: 0x%8x with size %d\n", str, i, burst_req_o[i].src, burst_req_o[i].dst, burst_req_o[i].num_bytes);
      end
      f = $fopen("dma.log", "a");
      $fwrite(f, str);
      $fclose(f);
    end
  end
  // pragma translate_on

endmodule
