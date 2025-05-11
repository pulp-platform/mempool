// Copyright 2022 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Bowen Wang <bowwang@student.ethz.ch>
// This module split one burst request to several according to partition scheme selected
// This module is inserted between `idma_split_midend` and `idma_distribute_midend` in Terapool Cluster

`include "common_cells/registers.svh"

module idma_partition_midend 
  import mempool_pkg::SeqMemSizePerTile;
  import mempool_pkg::HeapSeqMemSizePerTile;
  import mempool_pkg::TCDMSize;
  #(
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
  input  logic [7:0] beat_cnt_i,
  input  logic       valid_i,
  output logic       ready_o,
  output meta_t      meta_o,
  // Partition 
  input  logic [7:0] group_factor_i,
  input  logic [7:0] allocated_size_i,
  output logic       partition_req_valid_o,
  input  logic       part_beat_cnt_rst_i,
  // Master
  output burst_req_t burst_req_o,
  output logic       valid_o,
  input  logic       ready_i,
  input  meta_t      meta_i
);

  // DmaRegionWidth covered by each Tile in [bytes]
  // DmaRegionWidth = #banks*4 = 4096*4     [bytes]
  // TileDmaRegionWidth        = 32*4       [bytes]
  typedef logic [AddrWidth-1:0] addr_t;
  // log2(4096*4)= 14 = TileIdBits + ConstBits = 7 + 7
  localparam DmaRegionAddressBits     = $clog2(DmaRegionWidth);
  localparam TileDmaRegionWidth       = DmaRegionWidth / 128; 

  // ------ Considering Partition Scheme ------ //
  // How many bits more need to consider in each partition
  logic [2:0]  shift_index;

  logic [AddrWidth-1:0] PartitionDmaRegionWidth;
  logic [AddrWidth-1:0] partition_mask;

  assign shift_index = (group_factor_i == 128) ? 0 : 
                       (group_factor_i == 64)  ? 1 : 
                       (group_factor_i == 32)  ? 2 : 
                       (group_factor_i == 16)  ? 3 : 
                       (group_factor_i == 8 )  ? 4 : 
                       (group_factor_i == 4 )  ? 5 : 
                       (group_factor_i == 2 )  ? 6 : 7;
  // #bytes covered in each partition per row
  assign PartitionDmaRegionWidth = TileDmaRegionWidth * group_factor_i; 
  // |--- 14 bits ---| Lower 14 bits in address
  //  1111111_1111111   GF=128
  //  0111111_1111111   GF=64
  //  0011111_1111111   GF=32
  assign partition_mask = {DmaRegionAddressBits{1'b1}} >> shift_index;

  // start_addr:        address in L1 of the current input burst
  // masked_start_addr: address bits within partition region
  addr_t start_addr, masked_start_addr;
  always_comb begin
    if (($unsigned(burst_req_i.src) >= DmaRegionStart) && ($unsigned(burst_req_i.src) < DmaRegionEnd)) begin
      // L1 ------> L2
      start_addr = burst_req_i.src;
    end else begin
      // L2 ------> L1
      start_addr = burst_req_i.dst;
    end
  end

  assign masked_start_addr = start_addr & partition_mask;

  // ------ Handle Meta Data ------ //
  logic req_valid;
  // Forward IDLE signal
  assign meta_o.backend_idle = meta_i.backend_idle;
  // Forward trans_complete signal as well
  assign meta_o.trans_complete = meta_i.trans_complete;
  // Send the req_valid signal back to split_midend
  assign partition_req_valid_o = req_valid;

  // ------ Split One request aligned to partition scheme ------ //
  enum logic {Idle, Busy} state_d, state_q;
  burst_req_t req_d, req_q;

  `FFARN(state_q, state_d, Idle, clk_i, rst_ni)
  `FFARN(req_q, req_d, '0, clk_i, rst_ni)

  
  // ------ Beat Counter Handler ------ //
  // When detecting `negedge` on beat_cnt_i, meaning a new DMA request starts, 
  // beat counter of partition need to reset 
  // beat_cnt_i: how many beats has been sent from split midend
  logic [7:0] beat_cnt_q;
  `FFARN(beat_cnt_q, beat_cnt_i, '0, clk_i, rst_ni)
  logic [7:0] rst_part_beat_cnt;
  assign rst_part_beat_cnt = {8{~( ~(|beat_cnt_i) & (|beat_cnt_q) )}}; // fall edge detect, negative reset

  logic [7:0] part_beat_cnt_d, part_beat_cnt_q, part_beat_cnt_pre_q;
  `FFARN(part_beat_cnt_pre_q, part_beat_cnt_d, '0, clk_i, rst_ni)
  assign part_beat_cnt_q = part_beat_cnt_pre_q & rst_part_beat_cnt;

  // figure out which partition targeting
  // only update if beat_cnt_i == 0 (first beat)
  logic [2:0]  pid_shift_index;
  assign pid_shift_index = (group_factor_i == 128) ? 7 : 
                           (group_factor_i == 64)  ? 6 : 
                           (group_factor_i == 32)  ? 5 : 
                           (group_factor_i == 16)  ? 4 : 
                           (group_factor_i == 8 )  ? 3 : 
                           (group_factor_i == 4 )  ? 2 : 
                           (group_factor_i == 2 )  ? 1 : 0; // TODO

  logic [6:0] part_id_d, part_id_q, part_id_mask;
  `FFARN(part_id_q, part_id_d, '0, clk_i, rst_ni)
  always_comb begin
    part_id_d = part_id_q;
    part_id_mask = {7{1'b1}};
    if (|beat_cnt_i == 0) begin
      part_id_d = (group_factor_i == 128) ? 0 : (start_addr >> (pid_shift_index + 7)) & (part_id_mask>>pid_shift_index);
    end
  end

  // ------ Shifter from new partition layout ------ //
  // maximum rows in each partition: 128
  // maximum number of partitions:   128

  logic [7:0] shift_row, shift_partition;
  logic [2:0] shift_index_sc;
  logic [7:0] mask_shift_row;
  always_comb begin
    case(allocated_size_i)
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

  assign shift_partition = part_beat_cnt_q >> shift_index_sc;
  assign mask_shift_row  = ~( {8{1'b1}}<<shift_index_sc );
  assign shift_row       = part_beat_cnt_q & mask_shift_row;


  always_comb begin
    state_d = state_q;
    req_d   = req_q;
    burst_req_o = '0;
    valid_o     = 1'b0;
    ready_o     = 1'b0;
    req_valid   = 1'b0;
    part_beat_cnt_d = part_beat_cnt_pre_q;
    if (rst_part_beat_cnt == 0) begin
      part_beat_cnt_d = '0;
    end
    if (part_beat_cnt_rst_i == 1) begin
      part_beat_cnt_d = '0;
    end

    // Input: burst request fits into L1 boundary
    unique case (state_q)
      Idle: begin
        if (valid_i) begin // one request ready from split_midend
          // 1.   Burst fits into one partition
          // 1.1  Current burst is the first one in the whole DMA request
          // 1.2  Current burst is the last  one in the whole DMA request 
          if (PartitionDmaRegionWidth-masked_start_addr >= burst_req_i.num_bytes)begin
            // increase part_beat_cnt
            part_beat_cnt_d = part_beat_cnt_q + ready_i;
            burst_req_o = burst_req_i;
            if (($unsigned(burst_req_i.src) >= DmaRegionStart) && ($unsigned(burst_req_i.src) < DmaRegionEnd)) begin
              // L1 ------> L2
              // correct addr = base addr       + row offset                                  + partition offset
              if(beat_cnt_i == 0)begin
                burst_req_o.src = burst_req_i.src + (part_beat_cnt_q-beat_cnt_i)*DmaRegionWidth;
              end else begin
                burst_req_o.src = burst_req_i.src + (part_beat_cnt_q-beat_cnt_i)*DmaRegionWidth + part_id_q*PartitionDmaRegionWidth;
              end
            end else begin
              // L2 ------> L1
              if (beat_cnt_i == 0) begin
                // handle 1.1
                // burst_req_o.dst = burst_req_i.dst + (part_beat_cnt_q-beat_cnt_i)*DmaRegionWidth;
                burst_req_o.dst = burst_req_i.dst + part_beat_cnt_q*DmaRegionWidth;
              end else begin
                // handle 1.2
                burst_req_o.dst = burst_req_i.dst + (part_beat_cnt_q-beat_cnt_i)*DmaRegionWidth + part_id_q*PartitionDmaRegionWidth;
              end
            end
            valid_o = 1'b1;
            ready_o = ready_i;
            req_valid = ready_i;
          // 2. prepare split one beat into several
          end else begin
            // store and acknowledge
            req_d = burst_req_i;
            ready_o = 1'b1;
            // keep: [src] [dest], modify: [num_bytes]
            burst_req_o = burst_req_i;
            burst_req_o.num_bytes = PartitionDmaRegionWidth-masked_start_addr;
            if (($unsigned(burst_req_i.src) >= DmaRegionStart) && ($unsigned(burst_req_i.src) < DmaRegionEnd)) begin
              // L1 ------> L2
              if (beat_cnt_i == 0) begin
                req_d.src       = burst_req_i.src + (part_beat_cnt_q-beat_cnt_i)*DmaRegionWidth;
                burst_req_o.src = burst_req_i.src + (part_beat_cnt_q-beat_cnt_i)*DmaRegionWidth;
              end else begin
                // correct old version
                req_d.src       = burst_req_i.src + (part_beat_cnt_q-beat_cnt_i)*DmaRegionWidth + part_id_q*PartitionDmaRegionWidth;
                burst_req_o.src = burst_req_i.src + (part_beat_cnt_q-beat_cnt_i)*DmaRegionWidth + part_id_q*PartitionDmaRegionWidth;
              end
            end else begin
              // L2 ------> L1
              if (beat_cnt_i == 0) begin
                // req_d.dst       = burst_req_i.dst + (part_beat_cnt_q-beat_cnt_i)*DmaRegionWidth;
                // burst_req_o.dst = burst_req_i.dst + (part_beat_cnt_q-beat_cnt_i)*DmaRegionWidth;
                req_d.dst       = burst_req_i.dst + shift_row*DmaRegionWidth + shift_partition*PartitionDmaRegionWidth;
                burst_req_o.dst = burst_req_i.dst + shift_row*DmaRegionWidth + shift_partition*PartitionDmaRegionWidth;
              end else begin
                req_d.dst       = burst_req_i.dst + (part_beat_cnt_q-beat_cnt_i)*DmaRegionWidth + part_id_q*PartitionDmaRegionWidth;
                burst_req_o.dst = burst_req_i.dst + (part_beat_cnt_q-beat_cnt_i)*DmaRegionWidth + part_id_q*PartitionDmaRegionWidth;
              end
            end
            // noftify downstream
            valid_o = 1'b1;
            if (ready_i) begin
              // increase partition beat cnt
              part_beat_cnt_d = part_beat_cnt_q + 1;
              // downstream is ready to receive, modify the stored req
              req_d.num_bytes -= PartitionDmaRegionWidth-masked_start_addr;
              if (($unsigned(burst_req_i.src) >= DmaRegionStart) && ($unsigned(burst_req_i.src) < DmaRegionEnd)) begin
                // L1 ------> L2
                req_d.src       += DmaRegionWidth-masked_start_addr;              // folded to second row
                req_d.dst       += PartitionDmaRegionWidth-masked_start_addr;
              end else begin
                // L2 ------> L1
                req_d.src       += PartitionDmaRegionWidth-masked_start_addr;
                // req_d.dst       += DmaRegionWidth-masked_start_addr;
                req_d.dst       += DmaRegionWidth-masked_start_addr;  // modification needed
              end
              req_valid        = 1'b1;  // one request sent, counter increment
            end
            state_d = Busy;
          end
        end
      end 

      Busy:  begin
        // get burst request from the stored one
        burst_req_o = req_q;
        valid_o = 1'b1;
        req_valid = ready_i;     // counter increment whenever one req sent to downstream
        if ($unsigned(req_q.num_bytes) <= $unsigned(PartitionDmaRegionWidth)) begin
          // last burst
          if (ready_i) begin
            state_d = Idle;
            // burst_req does not need to change 
            // increase partition beat cnt
            part_beat_cnt_d = part_beat_cnt_q + 1;
          end
        end else begin
          // middle bursts
          burst_req_o.num_bytes = PartitionDmaRegionWidth;
          if (ready_i) begin
            // increase partition beat cnt
            part_beat_cnt_d = part_beat_cnt_q + 1;
            req_d.num_bytes = req_q.num_bytes - PartitionDmaRegionWidth;
            if (($unsigned(req_q.src) >= DmaRegionStart) && ($unsigned(req_q.src) < DmaRegionEnd)) begin
              // L1 ------> L2
              req_d.src       = req_q.src + DmaRegionWidth;              // folded to second row
              req_d.dst       = req_q.dst + PartitionDmaRegionWidth;     // addr in L2 increases as usual
            end else begin
              // L2 ------> L1
              req_d.src       = req_q.src + PartitionDmaRegionWidth;
              // req_d.dst       = req_q.dst + DmaRegionWidth;
              if (shift_row == allocated_size_i-1) begin
                req_d.dst       = req_q.dst + PartitionDmaRegionWidth - shift_row*DmaRegionWidth;
              end else begin
                req_d.dst       = req_q.dst + DmaRegionWidth;
              end
            end
          end
        end
      end 

      default: /*do nothing*/;
    endcase 


  end

  // pragma translate_off
  int f;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    automatic string str;
    if (rst_ni && valid_i && ready_o) begin
      str = "\n[Partition] Got request\n";
      str = $sformatf("%sPartition: Request in: From: 0x%8x To: 0x%8x with size %d. Beat count: %d\n", str, burst_req_i.src, burst_req_i.dst, burst_req_i.num_bytes, beat_cnt_i);
      f = $fopen("dma.log", "a");
      $fwrite(f, str);
      $fclose(f);
    end
    if (rst_ni && valid_o && ready_i) begin
      str = $sformatf("Partition: From: 0x%8x To: 0x%8x with size %d. Partition beat count: %d. [part_id] %d\n", burst_req_o.src, burst_req_o.dst, burst_req_o.num_bytes, part_beat_cnt_q, part_id_q);
      // str = $sformatf("Debug Rst: [rst_part_beat_cnt] %d [beat_cnt_q] %d [beat_cnt_i] %d \n",rst_part_beat_cnt, beat_cnt_q, beat_cnt_i);
      f = $fopen("dma.log", "a");
      $fwrite(f, str);
      // str = $sformatf("Debug: [start_addr] %8x [GF] %d \n",start_addr, group_factor_i);
      // $fwrite(f, str);
      $fclose(f);
    end
  end
  // pragma translate_on

endmodule
