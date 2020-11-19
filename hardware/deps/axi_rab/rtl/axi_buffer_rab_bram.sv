// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

module axi_buffer_rab_bram
  #(
    parameter DATA_WIDTH,
    parameter BUFFER_DEPTH
    )
   (
    input logic                   clk,
    input logic                   rstn,

    // Downstream port
    output logic [DATA_WIDTH-1:0] data_out,
    output logic                  valid_out,
    input  logic                  ready_in,

    // Upstream port
    input  logic                  valid_in,
    input  logic [DATA_WIDTH-1:0] data_in,
    output logic                  ready_out,

    // Status and drop control
    output logic                  almost_full,
    output logic                  underfull,
    input  logic                  drop_req,
    // Number of items to drop.  As for AXI lengths, counting starts at zero, i.e., `drop_len == 0`
    // and `drop_req` means drop one item.
    input  logic [7:0]            drop_len
    );

  // The BRAM needs to be in "write-first" mode for first-word fall-through FIFO behavior.
  // To still push and pop simultaneously if the buffer is full, we internally increase the
  // buffer depth by 1.
  localparam ACT_BUFFER_DEPTH     = BUFFER_DEPTH+1;
  localparam ACT_LOG_BUFFER_DEPTH = $clog2(ACT_BUFFER_DEPTH+1);

  /**
    * Internal data structures
    */
  // Location to which we last wrote
  logic        [ACT_LOG_BUFFER_DEPTH-1:0] ptr_in_d,                   ptr_in_q;
  // Location from which we last sent
  logic        [ACT_LOG_BUFFER_DEPTH-1:0] ptr_out_d,                  ptr_out_q;
  // Required for fall-through behavior on the first word
  logic        [ACT_LOG_BUFFER_DEPTH-1:0] ptr_out_bram;
  // Number of elements in the buffer.  Can be negative if elements that have been dropped have not
  // yet been written.
  logic signed   [ACT_LOG_BUFFER_DEPTH:0] n_elems_d,                  n_elems_q;

  logic           [DATA_WIDTH-1:0]        data_out_bram, data_out_q;
  logic                                   valid_out_q;

  logic full;

  assign almost_full = (n_elems_q == BUFFER_DEPTH-1);
  assign full        = (n_elems_q == BUFFER_DEPTH);

  always_ff @(posedge clk, negedge rstn) begin
    if (~rstn) begin
      n_elems_q <= '0;
      ptr_in_q  <= '0;
      ptr_out_q <= '0;
    end else begin
      n_elems_q <= n_elems_d;
      ptr_in_q  <= ptr_in_d;
      ptr_out_q <= ptr_out_d;
    end
  end

  // Update the number of elements.
  always_comb begin
    n_elems_d = n_elems_q;
    if (drop_req) begin
      n_elems_d -= (drop_len + 1);
    end
    if (valid_in && ready_out) begin
      n_elems_d += 1;
    end
    if (valid_out && ready_in) begin
      n_elems_d -= 1;
    end
  end

  // Update the output pointer.
  always_comb begin
    ptr_out_d = ptr_out_q;
    if (drop_req) begin
      if ((ptr_out_q + drop_len + 1) > (ACT_BUFFER_DEPTH - 1)) begin
        ptr_out_d = drop_len + 1 - (ACT_BUFFER_DEPTH - ptr_out_q);
      end else begin
        ptr_out_d += (drop_len + 1);
      end
    end
    if (valid_out && ready_in) begin
      if (ptr_out_d == (ACT_BUFFER_DEPTH - 1)) begin
        ptr_out_d = '0;
      end else begin
        ptr_out_d += 1;
      end
    end
  end

  // The BRAM has a read latency of one cycle, so apply the new address one cycle earlier for
  // first-word fall-through FIFO behavior.
  //assign ptr_out_bram = (ptr_out_q == (ACT_BUFFER_DEPTH-1)) ? '0 : (ptr_out_q + 1);
  assign ptr_out_bram = ptr_out_d;

  // Update the input pointer.
  always_comb begin
    ptr_in_d = ptr_in_q;
    if (valid_in && ready_out) begin
      if (ptr_in_d == (ACT_BUFFER_DEPTH - 1)) begin
        ptr_in_d = '0;
      end else begin
        ptr_in_d += 1;
      end
    end
  end

  // Update output ports.
  assign valid_out = (n_elems_q > $signed(0));
  assign underfull = (n_elems_q < $signed(0));
  assign ready_out = ~full;

  ram_tp_write_first #(
    .ADDR_WIDTH ( ACT_LOG_BUFFER_DEPTH ),
    .DATA_WIDTH ( DATA_WIDTH           )
  )
  ram_tp_write_first_0
  (
    .clk   ( clk              ),
    .we    ( valid_in & ~full ),
    .addr0 ( ptr_in_q         ),
    .addr1 ( ptr_out_bram     ),
    .d_i   ( data_in          ),
    .d0_o  (                  ),
    .d1_o  ( data_out_bram    )
  );

  // When reading from/writing two the same address on both ports ("Write-Read Collision"),
  // the data on the read port is invalid (during the write cycle). In this implementation,
  // this can happen only when the buffer is empty. Thus, we forward the data from an
  // register in this case.
  always @(posedge clk) begin
    if (rstn == 1'b0) begin
      data_out_q <= 'b0;
    end else if ( (ptr_out_bram == ptr_in_q) && (valid_in && !full) ) begin
      data_out_q <= data_in;
    end
  end

  always @(posedge clk) begin
    if (rstn == 1'b0) begin
      valid_out_q <= 'b0;
    end else begin
      valid_out_q <= valid_out;
    end
  end

  // Drive output data
  always_comb begin
    if (valid_out && !valid_out_q) begin // We have just written to an empty FIFO
      data_out = data_out_q;
    end else begin
      data_out = data_out_bram;
    end
  end

endmodule
