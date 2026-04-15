// Copyright 2022 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Samuel Riedel <sriedel@iis.ee.ethz.ch>
// Bowen Wang <bowwang@student.ethz.ch>
// Marco Bertuletti <mbertuletti@iis.ee.ethz.ch>

`include "common_cells/registers.svh"

module idma_split_midend #(
  parameter int unsigned DmaRegionWidth = 1, // [B] Region that one port covers in bytes
  parameter int unsigned DmaRegionStart = 32'h0000_0000,
  parameter int unsigned DmaRegionEnd   = 32'h1000_0000,
  parameter int unsigned AddrWidth      = 32,
`ifdef DAS
  parameter int unsigned NumTiles          = 64,
  parameter int unsigned NumBanksPerTile   = 32,
  parameter int unsigned TCDMSizePerBank   = 1024,
  parameter int unsigned NumDASPartitions  = 4,
  parameter int unsigned DASStartAddr      = 1024,
  parameter int unsigned NumTilesPerDma    = 16,
`endif
  parameter type         burst_req_t    = logic,
  parameter type         meta_t         = logic
) (
  input  logic       clk_i,
  input  logic       rst_ni,
`ifdef DAS
  // DAS signals
  input  logic [NumDASPartitions-1:0][$clog2(NumTiles):0] tiles_das_i,
  input  logic [NumDASPartitions-1:0][AddrWidth-1:0]      start_das_i,
  input  logic [NumDASPartitions-1:0][$clog2(NumTiles):0] rows_das_i,
  output logic [$clog2(NumTiles):0]                       rows_das_o,
`endif
  // Slave
  input  burst_req_t burst_req_i,
  input  logic       valid_i,
  output logic       ready_o,
  output meta_t      meta_o,
  // Master
  output burst_req_t burst_req_o,
  output logic       valid_o,
  input  logic       ready_i,
  input  meta_t      meta_i
);

  // ------ Parameter Settings ------ //
  localparam DmaRegionAddressBits = $clog2(DmaRegionWidth);
  typedef logic [AddrWidth-1:0] addr_t;

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

`ifdef DAS
  localparam TileDmaRegionWidth = DmaRegionWidth / NumTiles;
  logic [AddrWidth-1:0] PartitionDmaRegionWidth;
  localparam DmaBackendWidth = NumBanksPerTile*NumTilesPerDma*4; // 32banks*8Tiles*4bytes

  // ------ Address translation ------ //
  // Only the address in L1 SPM will be scrambled
  logic [AddrWidth-1:0] post_scramble_src;
  logic [AddrWidth-1:0] post_scramble_dst;
  logic [$clog2(NumTiles):0] tiles_das_src,   tiles_das_dst,   tiles_das_sel;
  logic [$clog2(NumTiles):0] rows_das_src, rows_das_dst, rows_das_sel;

  assign tiles_das_sel   = tiles_das_src   | tiles_das_dst;
  assign rows_das_sel = rows_das_src | rows_das_dst;
  assign PartitionDmaRegionWidth = TileDmaRegionWidth * tiles_das_sel;

  idma_address_scrambler #(
    .AddrWidth        (AddrWidth       ),
    .NumTiles         (NumTiles        ),
    .NumBanksPerTile  (NumBanksPerTile ),
    .Bypass           (0               ),
    .NumDASPartitions (NumDASPartitions),
    .TCDMSizePerBank  (TCDMSizePerBank )
  ) i_idma_address_scrambler_src (
    .address_i          (burst_req_i.src),
    .num_bytes_i        (burst_req_i.num_bytes),
    .tiles_das_i        (tiles_das_i),
    .rows_das_i         (rows_das_i),
    .start_das_i        (start_das_i),
    .tiles_das_o        (tiles_das_src),
    .rows_das_o         (rows_das_src),
    .address_o          (post_scramble_src)
  );

  idma_address_scrambler #(
    .AddrWidth        (AddrWidth       ),
    .NumTiles         (NumTiles        ),
    .NumBanksPerTile  (NumBanksPerTile ),
    .Bypass           (0               ),
    .NumDASPartitions (NumDASPartitions),
    .TCDMSizePerBank  (TCDMSizePerBank )
  ) i_idma_address_scrambler_dst (
    .address_i          (burst_req_i.dst),
    .num_bytes_i        (burst_req_i.num_bytes),
    .tiles_das_i        (tiles_das_i),
    .rows_das_i         (rows_das_i),
    .start_das_i        (start_das_i),
    .tiles_das_o        (tiles_das_dst),
    .rows_das_o         (rows_das_dst),
    .address_o          (post_scramble_dst)
  );

  // ------ Filter out address in L1 SPM ------ //
  addr_t start_addr;
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
  end

  // ------ Partition Row Offset Computation ------ //
  // A DAS partition maps data onto a 2D grid: `tiles_das` tiles wide, `rows_das`
  // rows tall. Each row holds `PartitionDmaRegionWidth` bytes. Transfers must be
  // split at row boundaries because consecutive rows are `DmaRegionWidth` apart
  // in physical SPM (not contiguous), even though the DRAM side is contiguous.

  // log2(tiles_das_sel): number of tile-index bits in the active partition
  logic [$clog2(NumTiles):0] log2_tiles;
  // Bitmask to extract the byte offset within one partition row from the
  // scrambled address. Width = DmaRegionAddressBits - (TileIdBits - log2_tiles).
  logic [AddrWidth-1:0]      row_offset_mask;
  // Byte offset of the scrambled start address within its partition row.
  // Used to compute how much data fits in the first (possibly partial) row.
  addr_t                     start_row_offset;

  lzc #(
    .WIDTH ($clog2(NumTiles)+1),
    .MODE  (1'b0              )
  ) i_log2_tiles (
    .in_i    (tiles_das_sel),
    .cnt_o   (log2_tiles   ),
    .empty_o (/* Unused */  )
  );

  assign row_offset_mask  = {DmaRegionAddressBits{1'b1}} >> ($clog2(NumTiles) - log2_tiles);
  assign start_row_offset = start_addr & row_offset_mask;

  // ------ Beat Counter and Row/Column Index ------ //
  // The beat counter tracks sub-transfer progress through the partition's 2D
  // layout. It encodes a (row_idx, col_idx) pair:
  //   - Lower log2(rows_das) bits = row_idx (cycles through rows first)
  //   - Upper bits               = col_idx (advances after all rows complete)
  // Transfer order: row0-col0, row1-col0, ..., rowN-col0, row0-col1, ...
  logic [$clog2(NumTiles):0] beat_cnt_d, beat_cnt_q;
  `FFARN(beat_cnt_q, beat_cnt_d, '0, clk_i, rst_ni)

  // log2(rows_das_sel): number of row-index bits in the active partition
  logic [$clog2(NumTiles):0] log2_rows;
  // Bitmask to extract row index from the beat counter (lower log2_rows bits)
  logic [$clog2(NumTiles):0] row_idx_mask;
  // Current row index within the partition (0 .. rows_das-1)
  logic [$clog2(NumTiles):0] row_idx;
  // Current column index: how many full row sweeps have completed
  logic [$clog2(NumTiles):0] col_idx;

  lzc #(
    .WIDTH ($clog2(NumTiles)+1),
    .MODE  (1'b0              )
  ) i_log2_rows (
    .in_i    (rows_das_sel),
    .cnt_o   (log2_rows   ),
    .empty_o (/* Unused */ )
  );

  assign col_idx      = beat_cnt_q >> log2_rows;
  assign row_idx_mask = ~( {($clog2(NumTiles) + 1){1'b1}} << log2_rows );
  assign row_idx      = beat_cnt_q & row_idx_mask;
`else
  // ------ Filter out address in L1 SPM ------ //
  addr_t start_addr;
  always_comb begin
    if (($unsigned(burst_req_i.src) >= DmaRegionStart) && ($unsigned(burst_req_i.src) < DmaRegionEnd)) begin
      start_addr = burst_req_i.src;
    end else begin
      start_addr = burst_req_i.dst;
    end
  end
`endif

  // ------ Split requests ------ //
  enum logic {Idle, Busy} state_d, state_q;
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

`ifdef DAS
    rows_das_o = rows_das_sel;
    beat_cnt_d = beat_cnt_q;
    if (num_trans_q == 1 && num_trans_d == 0) begin
      beat_cnt_d = 0;
    end
`endif

    unique case (state_q)
      Idle: begin
        if (valid_i) begin // Splitting required
`ifdef DAS
          if ((PartitionDmaRegionWidth-start_row_offset) >= burst_req_i.num_bytes) begin
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
            burst_req_o.num_bytes = PartitionDmaRegionWidth-start_row_offset;
            // TODO (bowwang): parameterize
            req_d.num_bytes = (tiles_das_sel <= NumTilesPerDma) ? (rows_das_sel*DmaBackendWidth) : (rows_das_sel*PartitionDmaRegionWidth);
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
              req_d.num_bytes -= PartitionDmaRegionWidth-start_row_offset;
              if (spm2dram) begin
                req_d.src += DmaRegionWidth-start_row_offset;
                req_d.dst += PartitionDmaRegionWidth-start_row_offset;
              end else begin
                req_d.src += PartitionDmaRegionWidth-start_row_offset;
                req_d.dst += DmaRegionWidth-start_row_offset;
              end
              req_valid  = 1'b1;
              beat_cnt_d = 1;
            end
            state_d = Busy;
          end
`else
          if (DmaRegionWidth-start_addr[DmaRegionAddressBits-1:0] >= burst_req_i.num_bytes) begin
            // No splitting required, just forward
            burst_req_o = burst_req_i;
            valid_o = 1'b1;
            ready_o = ready_i;
            req_valid = ready_i;
          end else begin
            // Store and acknowledge
            req_d = burst_req_i;
            ready_o = 1'b1;
            // Feed through the first request
            burst_req_o = burst_req_i;
            // Modify it's size
            burst_req_o.num_bytes = DmaRegionWidth-start_addr[DmaRegionAddressBits-1:0];
            // Forward request
            valid_o = 1'b1;
            if (ready_i) begin
              // Increment the address and reduce the number of outstanding splits
              req_d.num_bytes -= DmaRegionWidth-start_addr[DmaRegionAddressBits-1:0];
              req_d.src += DmaRegionWidth-start_addr[DmaRegionAddressBits-1:0];
              req_d.dst += DmaRegionWidth-start_addr[DmaRegionAddressBits-1:0];
              req_valid = 1'b1;
            end
            state_d = Busy;
          end
`endif
        end
      end
      Busy: begin
        // Sent next burst from split.
        burst_req_o = req_q;
        valid_o = 1'b1;
        req_valid = ready_i;
`ifdef DAS
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
            // SPM address stride: consecutive partition rows are DmaRegionWidth
            // apart in physical memory. At the last row (row_idx == rows_das-1),
            // wrap back to row 0 and advance to the next column within the row.
            // DRAM address always advances contiguously by PartitionDmaRegionWidth.
            if (spm2dram) begin
              if (row_idx == rows_das_sel-1) begin
                req_d.src = req_q.src + PartitionDmaRegionWidth - row_idx*DmaRegionWidth;
              end else begin
                req_d.src = req_q.src + DmaRegionWidth;
              end
              req_d.dst = req_q.dst + PartitionDmaRegionWidth;
            end else begin
              req_d.src = req_q.src + PartitionDmaRegionWidth;
              if (row_idx == rows_das_sel-1) begin
                req_d.dst   = req_q.dst + PartitionDmaRegionWidth - row_idx*DmaRegionWidth;
              end else begin
                req_d.dst = req_q.dst + DmaRegionWidth;
              end
            end// spm2dram
          end // ready_i
        end
`else
        if ($unsigned(req_q.num_bytes) <= $unsigned(DmaRegionWidth)) begin
          // Last split
          if (ready_i) begin
            state_d = Idle;
          end
        end else begin
          // Clip size and increment address
          burst_req_o.num_bytes = DmaRegionWidth;
          if (ready_i) begin
            req_d.num_bytes = req_q.num_bytes - DmaRegionWidth;
            req_d.src = req_q.src + DmaRegionWidth;
            req_d.dst = req_q.dst + DmaRegionWidth;
          end
        end
`endif
      end
      default: /*do nothing*/;
    endcase
  end

  // pragma translate_off
  int f;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    automatic string str;
    if (rst_ni && valid_i && ready_o) begin
      str = "\n\n[idma_split_midend] Got request\n";
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
