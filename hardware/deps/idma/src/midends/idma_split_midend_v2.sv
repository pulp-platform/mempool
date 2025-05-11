// Copyright 2022 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Samuel Riedel <sriedel@iis.ee.ethz.ch>
// Bowen Wang    <bowwang@student.ethz.ch> 


// The Split Midend (v2) slice one burst request aligned to partition boundary, instead of 
// L1 SPM boundary as in v1.

`include "common_cells/registers.svh"

module idma_split_midend_v2 #(
  parameter int unsigned DmaRegionWidth = 1, // [B] Region that one port covers in bytes
  parameter int unsigned DmaRegionStart = 32'h0000_0000,
  parameter int unsigned DmaRegionEnd   = 32'h1000_0000,
  parameter int unsigned AddrWidth      = 32,
  parameter type         burst_req_t    = logic,
  parameter type         meta_t         = logic
) (
  input  logic       clk_i,
  input  logic       rst_ni,
  // Slave
  input  burst_req_t burst_req_i,
  input  logic       valid_i,
  output logic       ready_o,
  output meta_t      meta_o,

  // Partition related signals
  input  logic [1:0]                dma_mode_i,
  input  logic [3:0][7:0]           group_factor_i,
  input  logic [3:0][7:0]           allocated_size_i,
  input  logic [3:0][AddrWidth-1:0] start_addr_scheme_i,
  output logic [7:0]                allocated_size_o,

  // Master
  output burst_req_t burst_req_o,
  output logic       valid_o,
  input  logic       ready_i,
  input  meta_t      meta_i
);

  // ------ Parameter Settings ------ //
  typedef logic [AddrWidth-1:0] addr_t;
  localparam DmaRegionAddressBits = $clog2(DmaRegionWidth);
  localparam TileDmaRegionWidth       = DmaRegionWidth / 128;
  logic [AddrWidth-1:0] PartitionDmaRegionWidth;

  localparam DmaBackendWidth = 32*8*4; // 32banks*8Tiles*4bytes 

  // ------ Address translation ------ //
  // Only the address in L1 SPM will be scrambled
  logic [AddrWidth-1:0] post_scramble_src;
  logic [AddrWidth-1:0] post_scramble_dst;
  logic [7:0]           group_factor_src,   group_factor_dst,   group_factor_sel;
  logic [7:0]           allocated_size_src, allocated_size_dst, allocated_size_sel;

  assign group_factor_sel   = group_factor_src   | group_factor_dst;
  assign allocated_size_sel = allocated_size_src | allocated_size_dst;
  assign PartitionDmaRegionWidth = TileDmaRegionWidth * group_factor_sel;

  idma_address_scrambler i_idma_address_scrambler_src (
    .address_i          (burst_req_i.src),
    .num_bytes_i        (burst_req_i.num_bytes),
    .group_factor_i     (group_factor_i),
    .allocated_size_i   (allocated_size_i),
    .start_addr_scheme_i(start_addr_scheme_i),
    .group_factor_o     (group_factor_src),
    .allocated_size_o   (allocated_size_src),
    .address_o          (post_scramble_src)
  );

  idma_address_scrambler i_idma_address_scrambler_dst (
    .address_i          (burst_req_i.dst),
    .num_bytes_i        (burst_req_i.num_bytes),
    .group_factor_i     (group_factor_i),
    .allocated_size_i   (allocated_size_i),
    .start_addr_scheme_i(start_addr_scheme_i),
    .group_factor_o     (group_factor_dst),
    .allocated_size_o   (allocated_size_dst),
    .address_o          (post_scramble_dst)
  );

  // ------ Filter out address in L1 SPM ------ //
  addr_t start_addr, end_addr;
  logic  spm2dram;

  always_comb begin
    spm2dram = 0;
    if (($unsigned(burst_req_i.src) >= DmaRegionStart) && ($unsigned(burst_req_i.src) < DmaRegionEnd)) begin
      start_addr = post_scramble_src;
      spm2dram = 1;
    end else begin
      start_addr = post_scramble_dst;
      spm2dram = 0;
    end
    // not used
    end_addr = start_addr + burst_req_i.num_bytes; 
  end

  // ------ Considering Partition Scheme ------ //
  logic [2:0]           shift_index;
  logic [AddrWidth-1:0] partition_mask;
  addr_t                masked_start_addr;

  always_comb begin
      case(group_factor_sel)
          128: shift_index = 0;
          64:  shift_index = 1;
          32:  shift_index = 2;
          16:  shift_index = 3;
          8:   shift_index = 4;
          4:   shift_index = 5;
          2:   shift_index = 6;
          default: shift_index = 7;
      endcase
  end

  assign partition_mask = {DmaRegionAddressBits{1'b1}} >> shift_index;
  assign masked_start_addr = start_addr & partition_mask;

  // ------ Handle Metadata ------ //
  // Forward idle signal and count the trans_comlete signal
  logic req_valid;
  logic [31:0] num_trans_d, num_trans_q;

  assign meta_o.backend_idle = meta_i.backend_idle;
  always_comb begin
    num_trans_d = num_trans_q;
    meta_o.trans_complete = 1'b0;

    if (req_valid) begin
      num_trans_d += 1;
    end
    if (meta_i.trans_complete) begin
      num_trans_d -= 1;
    end
    if (num_trans_q == 1 && num_trans_d == 0) begin
      meta_o.trans_complete = 1'b1;
    end
  end
  `FF(num_trans_q, num_trans_d, '0, clk_i, rst_ni)

  // ------ Beat Counter and Shifter Handler ------ //
  logic [7:0] beat_cnt_d, beat_cnt_q;
  `FFARN(beat_cnt_q, beat_cnt_d, '0, clk_i, rst_ni)

  logic [7:0] shift_row, shift_partition;
  logic [2:0] shift_index_sc;
  logic [7:0] mask_shift_row;

  always_comb begin
    case(allocated_size_sel)
        128: shift_index_sc = 7;
        64:  shift_index_sc = 6;
        32:  shift_index_sc = 5;
        16:  shift_index_sc = 4;
        8:   shift_index_sc = 3;
        4:   shift_index_sc = 2;
        2:   shift_index_sc = 1;
        default: shift_index_sc = 0;
    endcase
  end 

  assign shift_partition = beat_cnt_q >> shift_index_sc;
  assign mask_shift_row  = ~( {8{1'b1}}<<shift_index_sc );
  assign shift_row       = beat_cnt_q & mask_shift_row;

  // ------ Duplication ------ //
  addr_t dup_start_addr_d, dup_start_addr_q;
  `FF(dup_start_addr_q, dup_start_addr_d, '0, clk_i, rst_ni)

  // ------ Split requests ------ //
  enum logic       {Idle, Busy} state_d, state_q;
  burst_req_t req_d, req_q;

  `FFARN(state_q, state_d, Idle, clk_i, rst_ni)
  `FFARN(req_q, req_d, '0, clk_i, rst_ni)

  always_comb begin
    state_d = state_q;
    req_d = req_q;

    burst_req_o = '0;
    valid_o = 1'b0;
    ready_o = 1'b0;
    req_valid = 1'b0;

    allocated_size_o = allocated_size_sel;

    beat_cnt_d = beat_cnt_q;
    if (num_trans_q == 1 && num_trans_d == 0) begin 
      beat_cnt_d = 0;
    end

    dup_start_addr_d = dup_start_addr_q;

    unique case (state_q)
      Idle: begin
        if (valid_i) begin 
          unique case (dma_mode_i)
            // ------ Std Mode ------ //
            2'b00: begin 
              if ( (DmaRegionWidth-start_addr[DmaRegionAddressBits-1:0]) >= burst_req_i.num_bytes) begin
                burst_req_o = burst_req_i;
                valid_o = 1'b1;
                ready_o = ready_i;
                req_valid = ready_i;
              end else begin
                // Store and acknowledge
                req_d = burst_req_i;
                ready_o = 1'b1;
                burst_req_o = burst_req_i;
                // Calculate the size for the 1st burst
                burst_req_o.num_bytes = DmaRegionWidth-start_addr[DmaRegionAddressBits-1:0];
                valid_o = 1'b1;

                // Modify the stored info after first beat sent
                if (ready_i) begin
                  req_d.num_bytes -= DmaRegionWidth-start_addr[DmaRegionAddressBits-1:0];
                  req_d.src += DmaRegionWidth-start_addr[DmaRegionAddressBits-1:0];
                  req_d.dst += DmaRegionWidth-start_addr[DmaRegionAddressBits-1:0];
                  req_valid = 1'b1;
                end
                state_d = Busy;
              end
            end

            // ------ Fast Mode ------ //
            2'b01: begin  
              if ( (PartitionDmaRegionWidth-masked_start_addr) >= burst_req_i.num_bytes ) begin
                burst_req_o = burst_req_i;
                // Address in SPM need to be translated back to physical address
                if (spm2dram) begin
                  burst_req_o.src = post_scramble_src;
                end else begin
                  burst_req_o.dst = post_scramble_dst;
                end
                valid_o = 1'b1;
                ready_o = ready_i;
                req_valid = ready_i;
              end else begin
                // Store and acknowledge
                req_d = burst_req_i;
                ready_o = 1'b1;
                burst_req_o = burst_req_i;
                // Calculate the size for the 1st burst
                burst_req_o.num_bytes = PartitionDmaRegionWidth-masked_start_addr;
                // TODO (bowwang): parameterize
                req_d.num_bytes       = (group_factor_sel <= 8) ? (allocated_size_sel*DmaBackendWidth) : (allocated_size_sel*PartitionDmaRegionWidth);
                if (spm2dram) begin
                  burst_req_o.src = post_scramble_src;
                  req_d.src       = post_scramble_src;
                end else begin
                  burst_req_o.dst = post_scramble_dst;
                  req_d.dst       = post_scramble_dst;
                end
                valid_o = 1'b1;

                // Modify the stored info after first beat sent
                if (ready_i) begin
                  // TODO (bowwang): May not be mecessary to consider alignment
                  req_d.num_bytes -= PartitionDmaRegionWidth-masked_start_addr;
                  if (spm2dram) begin
                    req_d.src += DmaRegionWidth-masked_start_addr;
                    req_d.dst += PartitionDmaRegionWidth-masked_start_addr;
                  end else begin
                    req_d.src += PartitionDmaRegionWidth-masked_start_addr;
                    req_d.dst += DmaRegionWidth-masked_start_addr;
                  end
                  req_valid  = 1'b1;
                  beat_cnt_d = 1;
                end
                state_d = Busy;
              end
            end 

            // ------ Duplicate Mode ------ //
            2'b10: begin  
              if ( (PartitionDmaRegionWidth-masked_start_addr) >= burst_req_i.num_bytes ) begin
                burst_req_o = burst_req_i;
                // Address in SPM need to be translated back to physical address
                if (spm2dram) begin
                  burst_req_o.src = post_scramble_src;
                end else begin
                  burst_req_o.dst = post_scramble_dst;
                end
                valid_o = 1'b1;
                ready_o = ready_i;
                req_valid = ready_i;
              end else begin
                // Store and acknowledge
                req_d = burst_req_i;
                ready_o = 1'b1;
                burst_req_o = burst_req_i;
                // Calculate the size for the 1st burst
                burst_req_o.num_bytes = PartitionDmaRegionWidth-masked_start_addr;
                // TODO (bowwang): parameterize
                req_d.num_bytes = (group_factor_sel <= 8) ? (allocated_size_sel*DmaBackendWidth) : (allocated_size_sel*PartitionDmaRegionWidth);
                dup_start_addr_d = burst_req_i.src;
                if (spm2dram) begin
                  burst_req_o.src = post_scramble_src;
                  req_d.src       = post_scramble_src;
                end else begin
                  burst_req_o.dst = post_scramble_dst;
                  req_d.dst       = post_scramble_dst;
                end
                valid_o = 1'b1;

                // Modify the stored info after first beat sent
                if (ready_i) begin
                  // TODO (bowwang): May not be mecessary to consider alignment
                  req_d.num_bytes -= PartitionDmaRegionWidth-masked_start_addr;
                  if (spm2dram) begin
                    req_d.src += DmaRegionWidth-masked_start_addr;
                    req_d.dst += PartitionDmaRegionWidth-masked_start_addr;
                  end else begin
                    req_d.src += PartitionDmaRegionWidth-masked_start_addr;
                    req_d.dst += DmaRegionWidth-masked_start_addr;
                  end
                  req_valid  = 1'b1;
                  beat_cnt_d = 1;
                end
                state_d = Busy;
              end
            end 

            2'b11: begin  // Partition_Std Mode
              if ( (PartitionDmaRegionWidth-masked_start_addr) >= burst_req_i.num_bytes ) begin
                burst_req_o = burst_req_i;
                // Address in SPM need to be translated back to physical address
                if (spm2dram) begin
                  burst_req_o.src = post_scramble_src;
                end else begin
                  burst_req_o.dst = post_scramble_dst;
                end
                valid_o = 1'b1;
                ready_o = ready_i;
                req_valid = ready_i;
              end else begin
                // Store and acknowledge
                req_d = burst_req_i;
                ready_o = 1'b1;
                burst_req_o = burst_req_i;
                // Calculate the size for the 1st burst
                burst_req_o.num_bytes = PartitionDmaRegionWidth-masked_start_addr;
                if (spm2dram) begin
                  burst_req_o.src = post_scramble_src;
                  req_d.src       = post_scramble_src;
                end else begin
                  burst_req_o.dst = post_scramble_dst;
                  req_d.dst       = post_scramble_dst;
                end
                valid_o = 1'b1;

                // Modify the stored info after first beat sent
                if (ready_i) begin
                  // TODO (bowwang): May not be mecessary to consider alignment
                  req_d.num_bytes -= PartitionDmaRegionWidth-masked_start_addr;
                  if (spm2dram) begin
                    req_d.src += DmaRegionWidth-masked_start_addr;
                    req_d.dst += PartitionDmaRegionWidth-masked_start_addr;
                  end else begin
                    req_d.src += PartitionDmaRegionWidth-masked_start_addr;
                    req_d.dst += DmaRegionWidth-masked_start_addr;
                  end
                  req_valid  = 1'b1;
                  beat_cnt_d = 1;
                end
                state_d = Busy;
              end
            end 

            default: /*do nothing*/;
          endcase
        end
      end // Idle

      Busy: begin
        // Sent next burst from split.
        burst_req_o = req_q;
        valid_o = 1'b1;
        req_valid = ready_i;

        unique case (dma_mode_i)
          // ------ Std Mode ------ //
          2'b00: begin
            if ($unsigned(req_q.num_bytes) <= $unsigned(DmaRegionWidth)) begin
              if (ready_i) begin
                state_d = Idle;
              end
            end else begin
              burst_req_o.num_bytes = DmaRegionWidth;
              if (ready_i) begin
                req_d.num_bytes = req_q.num_bytes - DmaRegionWidth;
                req_d.src = req_q.src + DmaRegionWidth;
                req_d.dst = req_q.dst + DmaRegionWidth;
              end
            end
          end 

          2'b01,
          2'b10, 
          2'b11: begin
            if ($unsigned(req_q.num_bytes) <= $unsigned(PartitionDmaRegionWidth)) begin
              // Last split
              if (ready_i) begin
                state_d = Idle;
                beat_cnt_d = beat_cnt_q + 1;
              end
            end else begin
              burst_req_o.num_bytes = PartitionDmaRegionWidth;
              if (ready_i) begin
                req_d.num_bytes = req_q.num_bytes - PartitionDmaRegionWidth;
                beat_cnt_d = beat_cnt_q + 1;

                if (spm2dram) begin
                  if (shift_row == allocated_size_sel-1) begin
                    req_d.src       = req_q.src + PartitionDmaRegionWidth - shift_row*DmaRegionWidth;
                  end else begin
                    req_d.src       = req_q.src + DmaRegionWidth;
                  end
                  req_d.dst = req_q.dst + PartitionDmaRegionWidth;
                end else begin
                  req_d.src = req_q.src + PartitionDmaRegionWidth;
                  if (shift_row == allocated_size_sel-1) begin
                    req_d.dst       = req_q.dst + PartitionDmaRegionWidth - shift_row*DmaRegionWidth;
                    if (dma_mode_i == 2'b10) begin // duplication mode: recover start adddr
                      req_d.src     = dup_start_addr_q;
                    end
                  end else begin
                    req_d.dst       = req_q.dst + DmaRegionWidth;
                  end
                end// spm2dram
              end // ready_i
            end
          end // case {01, 10, 11}

          default: /*do nothing*/;
        endcase

      end // Busy
      default: /*do nothing*/;
    endcase
  end

  // pragma translate_off
  int f;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    automatic string str;
    if (rst_ni && valid_i && ready_o) begin
      str = "\n\n[idma_split_midend_v2] Got request\n";
      str = $sformatf("%sSplit: Request in: From: 0x%8x To: 0x%8x with size %d\n", str, burst_req_i.src, burst_req_i.dst, burst_req_i.num_bytes);
      f = $fopen("dma.log", "a");
      $fwrite(f, str);
      $fclose(f);
    end
    if (rst_ni && valid_o && ready_i) begin
      str = $sformatf("Split: Out %6d: From: 0x%8x To: 0x%8x with size %d, start_addr 0x%8x.\n", num_trans_q, burst_req_o.src, burst_req_o.dst, burst_req_o.num_bytes, start_addr);
      f = $fopen("dma.log", "a");
      $fwrite(f, str);
      $fclose(f);
    end
  end
  // pragma translate_on

endmodule
