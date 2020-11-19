// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

//`define MULTI_HIT_FULL_SET

module check_ram
  #(
    parameter ADDR_WIDTH     = 32,
    parameter RAM_DATA_WIDTH = 32,
    parameter PAGE_SIZE      = 4096, // 4kB
    parameter SET_WIDTH      = 5,
    parameter OFFSET_WIDTH   = 4
    )
  (
   input  logic                                clk_i,
   input  logic                                rst_ni,
   input  logic [ADDR_WIDTH-1:0]               in_addr_min,
   input  logic [ADDR_WIDTH-1:0]               in_addr_max, // not used unless partial match mode is enabled
   input  logic                                rw_type, // 1 => write, 0=> read
   input  logic                                partial_match, // with partial matches the hit_addr is not reliable
   input  logic                                ram_we,
   input  logic [SET_WIDTH+OFFSET_WIDTH+1-1:0] port0_addr,
   input  logic [SET_WIDTH+OFFSET_WIDTH+1-1:0] port1_addr,
   input  logic [RAM_DATA_WIDTH-1:0]           ram_wdata,
   input  logic                                output_sent,
   input  logic                                output_valid,
   input  logic [OFFSET_WIDTH-1:0]             offset_addr_d,
   output logic [SET_WIDTH+OFFSET_WIDTH+1-1:0] hit_addr,
   output logic                                master,
   output logic                                hit,
   output logic                                multi_hit,
   output logic                                prot
   );

   localparam IGNORE_LSB = $clog2(PAGE_SIZE); // 12

   logic [RAM_DATA_WIDTH-1:0]           port0_data_o, port1_data_o; // RAM read data outputs
   logic                                port0_hit, port1_hit; // Ram output matches in_addr

   logic [SET_WIDTH+OFFSET_WIDTH+1-1:0] port0_addr_saved, port1_addr_saved;

   // Hit FSM Signals
   typedef enum                         logic {SEARCH, HIT} hit_state_t;
   hit_state_t                          hit_SP; // Hit FSM state
   hit_state_t                          hit_SN; // Hit FSM next state

   // Multi Hit FSM signals
`ifdef MULTI_HIT_FULL_SET
   typedef enum                         logic[1:0] {NO_HITS, ONE_HIT, MULTI_HIT} multi_state_t;
   multi_state_t                        multi_SP; // Multi Hit FSM state
   multi_state_t                        multi_SN; // Multi Hit FSM next state

   logic [SET_WIDTH+OFFSET_WIDTH+1-1:0] hit_addr_saved;
   logic                                master_saved;
`endif

  //// --------------- Block RAM (Dual Port) -------------- ////

  // The outputs of the BRAMs are only valid if in the previous cycle:
  // 1. the inputs were valid, and
  // 2. the BRAM was not written to.
  // Otherwise, the outputs must be ignored which is controlled by the output_valid signal.
  // This signal is driven by the uppler level L2 TLB module.
  ram_tp_no_change #(
      .ADDR_WIDTH( SET_WIDTH+OFFSET_WIDTH+1 ),
      .DATA_WIDTH( RAM_DATA_WIDTH           )
    )
    ram_tp_no_change_0
    (
      .clk   ( clk_i         ),
      .we    ( ram_we        ),
      .addr0 ( port0_addr    ),
      .addr1 ( port1_addr    ),
      .d_i   ( ram_wdata     ),
      .d0_o  ( port0_data_o  ),
      .d1_o  ( port1_data_o  )
    );

   //// Check Ram Outputs
   always_comb begin
      if(partial_match) begin
         port0_hit = (port0_data_o[0] == 1'b1) && (in_addr_min[ADDR_WIDTH-1:IGNORE_LSB] <= port0_data_o[RAM_DATA_WIDTH-1:4])
                     && (port0_data_o[RAM_DATA_WIDTH-1:4] <= in_addr_max[ADDR_WIDTH-1:IGNORE_LSB]);
         port1_hit = (port1_data_o[0] == 1'b1) && (in_addr_min[ADDR_WIDTH-1:IGNORE_LSB] <= port1_data_o[RAM_DATA_WIDTH-1:4])
                     && (port1_data_o[RAM_DATA_WIDTH-1:4] <= in_addr_max[ADDR_WIDTH-1:IGNORE_LSB]);
      end else begin
         port0_hit = (port0_data_o[0] == 1'b1) && (in_addr_min[ADDR_WIDTH-1:IGNORE_LSB] == port0_data_o[RAM_DATA_WIDTH-1:4]);
         port1_hit = (port1_data_o[0] == 1'b1) && (in_addr_min[ADDR_WIDTH-1:IGNORE_LSB] == port1_data_o[RAM_DATA_WIDTH-1:4]);
      end
   end
   //// ----------------------------------------------------- /////

   //// ------------------- Check if Hit ------------------------ ////
   // FSM
   always_ff @(posedge clk_i) begin
      if (rst_ni == 0) begin
         hit_SP <= SEARCH;
      end else begin
         hit_SP <= hit_SN;
      end
   end

   always_ff @(posedge clk_i, negedge rst_ni) begin
      if (!rst_ni) begin
         port0_addr_saved <= '0;
         port1_addr_saved <= '0;
      end else begin
         port0_addr_saved <= port0_addr;
         port1_addr_saved <= port1_addr;
      end
   end

   always_comb begin
      hit_SN   = hit_SP;
      hit      = 1'b0;
      hit_addr = 0;
      master   = 1'b0;
      unique case(hit_SP)
        SEARCH :
          if (output_valid)
            if (port0_hit || port1_hit) begin
               hit_SN   = HIT;
               hit      = 1'b1;
               hit_addr = port0_hit ? {port0_addr_saved[SET_WIDTH+OFFSET_WIDTH:OFFSET_WIDTH], offset_addr_d} :
                          port1_hit ? {port1_addr_saved[SET_WIDTH+OFFSET_WIDTH:OFFSET_WIDTH], offset_addr_d} :
                          0;
               master   = port0_hit ? port0_data_o[3] :
                          port1_hit ? port1_data_o[3] :
                          1'b0;
            end

        HIT : begin
`ifdef MULTI_HIT_FULL_SET // Since the search continues after the first hit, it needs to be saved to be accessed later.
           hit      = 1'b1;
           hit_addr = hit_addr_saved;
           master   = master_saved;
`endif
           if (output_sent)
             hit_SN = SEARCH;
        end

        default : begin
           hit_SN = SEARCH;
        end
      endcase // case (hit_SP)
   end // always_comb begin

   //// ------------------------------------------- ////

   assign prot = output_valid && port0_hit ? ((~port0_data_o[2] && rw_type) || (~port0_data_o[1] && ~rw_type)) :
                 output_valid && port1_hit ? ((~port1_data_o[2] && rw_type) || (~port1_data_o[1] && ~rw_type)) :
                 1'b0;

   //// ------------------- Multi ------------------- ////
`ifdef MULTI_HIT_FULL_SET

   always_ff @(posedge clk_i) begin
      if (rst_ni == 0) begin
         hit_addr_saved <= 0;
         master_saved   <= 1'b0;
      end else if (output_valid) begin
         hit_addr_saved <= hit_addr;
         master_saved   <= master;
      end
   end

   // FSM
   always_ff @(posedge clk_i) begin
      if (rst_ni == 0) begin
         multi_SP <= NO_HITS;
      end else begin
         multi_SP <= multi_SN;
      end
   end

   always_comb begin
      multi_SN  = multi_SP;
      multi_hit = 1'b0;
      unique case(multi_SP)
        NO_HITS :
          if(output_valid && (port0_hit && port1_hit)) begin
             multi_SN  = MULTI_HIT;
             multi_hit = 1'b1;
          end else if(output_valid && (port0_hit || port1_hit))
            multi_SN = ONE_HIT;

        ONE_HIT :
          if(output_valid && (port0_hit || port1_hit)) begin
             multi_SN  = MULTI_HIT;
             multi_hit = 1'b1;
          end else if (output_sent)
            multi_SN = NO_HITS;

        MULTI_HIT : begin
          multi_hit = 1'b1;
           if (output_sent)
             multi_SN = NO_HITS;
        end

      endcase // case (multi_SP)
   end // always_comb begin

`else // !`ifdef MULTI_HIT_FULL_SET
   assign multi_hit = output_valid && port0_hit && port1_hit;
`endif // !`ifdef MULTI_HIT_FULL_SET
   //// ------------------------------------------- ////

endmodule
