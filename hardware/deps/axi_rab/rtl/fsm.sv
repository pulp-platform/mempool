// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

`timescale 1ns / 1ps

module fsm
  #(
    parameter AXI_M_ADDR_WIDTH = 40,
    parameter AXI_S_ADDR_WIDTH = 32,
    parameter AXI_ID_WIDTH     = 8,
    parameter AXI_USER_WIDTH   = 6
  )
  (
    input  logic                        Clk_CI,
    input  logic                        Rst_RBI,

    input  logic                        port1_addr_valid_i,
    input  logic                        port2_addr_valid_i,
    input  logic                        port1_sent_i,
    input  logic                        port2_sent_i,
    input  logic                        select_i,
    input  logic                        invalidate_i,
    input  logic                        no_hit_i,
    input  logic                        multi_hit_i,
    input  logic                        no_prot_i,
    input  logic                        prefetch_i,
    input  logic [AXI_M_ADDR_WIDTH-1:0] out_addr_i,
    input  logic                        cache_coherent_i,
    output logic                        port1_accept_o,
    output logic                        port1_drop_o,
    output logic                        port1_miss_o,
    output logic                        port2_accept_o,
    output logic                        port2_drop_o,
    output logic                        port2_miss_o,
    output logic [AXI_M_ADDR_WIDTH-1:0] out_addr_o,
    output logic                        cache_coherent_o,
    output logic                        miss_o,
    output logic                        multi_o,
    output logic                        prot_o,
    output logic                        prefetch_o,
    output logic                        invalidate_o,
    input  logic [AXI_S_ADDR_WIDTH-1:0] in_addr_min_i,
    input  logic [AXI_S_ADDR_WIDTH-1:0] in_addr_max_i,
    input  logic     [AXI_ID_WIDTH-1:0] in_id_i,
    input  logic                  [7:0] in_len_i,
    input  logic   [AXI_USER_WIDTH-1:0] in_user_i,
    output logic [AXI_S_ADDR_WIDTH-1:0] in_addr_min_o,
    output logic [AXI_S_ADDR_WIDTH-1:0] in_addr_max_o,
    output logic     [AXI_ID_WIDTH-1:0] in_id_o,
    output logic                  [7:0] in_len_o,
    output logic   [AXI_USER_WIDTH-1:0] in_user_o
  );

  //-------------Internal Signals----------------------

  typedef enum logic     [1:0] {IDLE, WAIT_SENT, WAIT_INVALIDATE} state_t;
  state_t                      state_SP; // Present state
  state_t                      state_SN; // Next State

  logic                        port1_accept_SN;
  logic                        port1_drop_SN;
  logic                        port1_miss_SN;
  logic                        port2_accept_SN;
  logic                        port2_drop_SN;
  logic                        port2_miss_SN;
  logic                        miss_SN;
  logic                        multi_SN;
  logic                        prot_SN;
  logic                        prefetch_SN;
  logic                        cache_coherent_SN;
  logic [AXI_M_ADDR_WIDTH-1:0] out_addr_DN;

  logic                        out_reg_en_S;

  //----------FSM comb------------------------------

  always_comb begin: FSM_COMBO
    state_SN          = state_SP;

    port1_accept_SN   = 1'b0;
    port1_drop_SN     = 1'b0;
    port1_miss_SN     = 1'b0;
    port2_accept_SN   = 1'b0;
    port2_drop_SN     = 1'b0;
    port2_miss_SN     = 1'b0;
    miss_SN           = 1'b0;
    multi_SN          = 1'b0;
    prot_SN           = 1'b0;
    prefetch_SN       = 1'b0;
    cache_coherent_SN = 1'b0;
    out_addr_DN       =   '0;

    out_reg_en_S      = 1'b0; // by default hold register output

    unique case(state_SP)
        IDLE : begin
          if ( invalidate_i ) begin
            // Stall during invalidation, forwarding the invalidation flag
            out_reg_en_S = 1'b1;
            state_SN     = WAIT_INVALIDATE;
          end else if ( (port1_addr_valid_i & select_i) | (port2_addr_valid_i & ~select_i) ) begin
            out_reg_en_S = 1'b1;
            state_SN     = WAIT_SENT;

            // Select inputs for output registers
            if (port1_addr_valid_i & select_i) begin
              port1_accept_SN = ~(no_hit_i | multi_hit_i | ~no_prot_i | prefetch_i);
              port1_drop_SN   =  (no_hit_i | multi_hit_i | ~no_prot_i | prefetch_i);
              port1_miss_SN   =   no_hit_i;
              port2_accept_SN = 1'b0;
              port2_drop_SN   = 1'b0;
              port2_miss_SN   = 1'b0;
            end else if (port2_addr_valid_i & ~select_i) begin
              port1_accept_SN = 1'b0;
              port1_drop_SN   = 1'b0;
              port1_miss_SN   = 1'b0;
              port2_accept_SN = ~(no_hit_i | multi_hit_i | ~no_prot_i | prefetch_i);
              port2_drop_SN   =  (no_hit_i | multi_hit_i | ~no_prot_i | prefetch_i);
              port2_miss_SN   =   no_hit_i;
            end

            miss_SN           = port1_miss_SN | port2_miss_SN;
            multi_SN          = multi_hit_i;
            prot_SN           = ~no_prot_i;
            prefetch_SN       = ~no_hit_i & prefetch_i;

            cache_coherent_SN = cache_coherent_i;
            out_addr_DN       = out_addr_i;
          end
        end

        WAIT_SENT : begin
          if ( port1_sent_i | port2_sent_i ) begin
            out_reg_en_S = 1'b1; // "clear" the register
            state_SN     = IDLE;
          end
        end

        WAIT_INVALIDATE : begin
          if ( ~invalidate_i ) begin
            out_reg_en_S = 1'b1; // clear invalidation
            state_SN     = IDLE;
          end
        end

        default : begin
           state_SN      = IDLE;
        end
      endcase
    end

  //----------FSM seq-------------------------------

  always_ff @(posedge Clk_CI, negedge Rst_RBI) begin: FSM_SEQ
    if (Rst_RBI == 1'b0)
      state_SP <= IDLE;
    else
      state_SP <= state_SN;
  end

  //----------Output seq--------------------------

  always_ff @(posedge Clk_CI, negedge Rst_RBI) begin: OUTPUT_SEQ
    if (Rst_RBI == 1'b0) begin
      port1_accept_o   = 1'b0;
      port1_drop_o     = 1'b0;
      port1_miss_o     = 1'b0;
      port2_accept_o   = 1'b0;
      port2_drop_o     = 1'b0;
      port2_miss_o     = 1'b0;
      miss_o           = 1'b0;
      multi_o          = 1'b0;
      prot_o           = 1'b0;
      prefetch_o       = 1'b0;
      invalidate_o     = 1'b0;
      cache_coherent_o = 1'b0;
      out_addr_o       =   '0;
      in_addr_min_o    =   '0;
      in_addr_max_o    =   '0;
      in_id_o          =   '0;
      in_len_o         =   '0;
      in_user_o        =   '0;
    end else if (out_reg_en_S == 1'b1) begin
      port1_accept_o   = port1_accept_SN;
      port1_drop_o     = port1_drop_SN;
      port1_miss_o     = port1_miss_SN;
      port2_accept_o   = port2_accept_SN;
      port2_drop_o     = port2_drop_SN;
      port2_miss_o     = port2_miss_SN;
      miss_o           = miss_SN;
      multi_o          = multi_SN;
      prot_o           = prot_SN;
      prefetch_o       = prefetch_SN;
      cache_coherent_o = cache_coherent_SN;
      out_addr_o       = out_addr_DN;
      invalidate_o     = invalidate_i;
      in_addr_min_o    = in_addr_min_i;
      in_addr_max_o    = in_addr_max_i;
      in_id_o          = in_id_i;
      in_len_o         = in_len_i;
      in_user_o        = in_user_i;
    end
  end // block: OUTPUT_SEQ

endmodule
