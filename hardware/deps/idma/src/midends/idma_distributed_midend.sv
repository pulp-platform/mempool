// Copyright 2022 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Samuel Riedel <sriedel@iis.ee.ethz.ch>

`include "common_cells/registers.svh"

module idma_distributed_midend #(
  parameter int unsigned NoMstPorts     = 1,
  parameter int unsigned DmaRegionWidth = 1, // [B] Region that one port covers in bytes
  parameter int unsigned DmaRegionStart = 32'h0000_0000,
  parameter int unsigned DmaRegionEnd   = 32'h1000_0000,
  parameter type         burst_req_t    = logic,
  parameter type         meta_t         = logic
) (
  input  logic                        clk_i,
  input  logic                        rst_ni,
  // Slave
  input  burst_req_t                  burst_req_i,
  input  logic                        valid_i,
  output logic                        ready_o,
  output meta_t                       meta_o,
  // Master
  output burst_req_t [NoMstPorts-1:0] burst_req_o,
  output logic       [NoMstPorts-1:0] valid_o,
  input  logic       [NoMstPorts-1:0] ready_i,
  input  meta_t      [NoMstPorts-1:0] meta_i
);

  localparam DmaRegionAddressBits = $clog2(DmaRegionWidth);
  localparam FullRegionAddressBits = $clog2(DmaRegionWidth*NoMstPorts);

  typedef logic [FullRegionAddressBits:0] full_addr_t;

  // Handle Metadata
  logic [NoMstPorts-1:0] trans_complete_d, trans_complete_q;
  logic [NoMstPorts-1:0] tie_off_trans_complete_d, tie_off_trans_complete_q;
  logic [NoMstPorts-1:0] backend_idle_d, backend_idle_q;
  assign meta_o.trans_complete = &trans_complete_q;
  assign meta_o.backend_idle = &backend_idle_q;

  // TODO We could have multiple outstanding requests per port, so we need multiple trans_complete_tie_offs
  always_comb begin
    trans_complete_d = trans_complete_q;
    backend_idle_d = backend_idle_q;
    for (int unsigned i = 0; i < NoMstPorts; i++) begin
      trans_complete_d[i] = trans_complete_q[i] | meta_i[i].trans_complete | tie_off_trans_complete_q[i];
      backend_idle_d[i] = meta_i[i].backend_idle;
    end
    if (meta_o.trans_complete) begin
      trans_complete_d = '0;
    end
  end
  `FF(trans_complete_q, trans_complete_d, '0, clk_i, rst_ni)
  `FF(tie_off_trans_complete_q, tie_off_trans_complete_d, '0, clk_i, rst_ni)
  `FF(backend_idle_q, backend_idle_d, '1, clk_i, rst_ni)

  // Fork
  logic [NoMstPorts-1:0] valid, ready;
  stream_fork #(
    .N_OUP (NoMstPorts)
  ) i_stream_fork (
    .clk_i   (clk_i  ),
    .rst_ni  (rst_ni ),
    .valid_i (valid_i),
    .ready_o (ready_o),
    .valid_o (valid  ),
    .ready_i (ready  )
  );

  full_addr_t src_addr, dst_addr, start_addr, end_addr;

  assign src_addr = burst_req_i.src[FullRegionAddressBits-1:0];
  assign dst_addr = burst_req_i.dst[FullRegionAddressBits-1:0];

  always_comb begin
    if (($unsigned(burst_req_i.src) >= DmaRegionStart) && ($unsigned(burst_req_i.src) < DmaRegionEnd)) begin
      start_addr = src_addr;
    end else begin
      start_addr = dst_addr;
    end
    end_addr = start_addr+burst_req_i.num_bytes;
    // Connect valid ready by default
    valid_o = valid;
    ready = ready_i;
    // Do not interfere with metadata per default
    tie_off_trans_complete_d = '0;
    for (int i = 0; i < NoMstPorts; i++) begin
      // Feed metadata through directly
      burst_req_o[i] = burst_req_i;
      // Feed through the address bits
      burst_req_o[i].src = burst_req_i.src;
      burst_req_o[i].dst = burst_req_i.dst;
      // Modify lower addresses bits and size
      if (($unsigned(start_addr) >= (i+1)*DmaRegionWidth) || ($unsigned(end_addr) <= i*DmaRegionWidth)) begin
        // We are not involved in the transfer
        burst_req_o[i].src = '0;
        burst_req_o[i].dst = '0;
        burst_req_o[i].num_bytes = 1;
        // Make handshake ourselves
        valid_o[i] = 1'b0;
        ready[i] = 1'b1;
        // Inject trans complete
        if (valid) begin
          tie_off_trans_complete_d[i] = 1'b1;
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
          burst_req_o[i].src = burst_req_i.src+i*DmaRegionWidth-start_addr[DmaRegionAddressBits-1:0];
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
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (rst_ni && valid_i && ready_o) begin
      $display("[idma_distributed_midend] Got request");
      $display("Request in: From: 0x%8x To: 0x%8x with size %d", burst_req_i.src, burst_req_i.dst, burst_req_i.num_bytes);
      for (int i = 0; i < NoMstPorts; i++) begin
        $display("Out %6d: From: 0x%8x To: 0x%8x with size %d", i, burst_req_o[i].src, burst_req_o[i].dst, burst_req_o[i].num_bytes);
      end
    end
  end
  // pragma translate_on

endmodule
