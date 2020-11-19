// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// --=========================================================================--
//
//  █████╗ ██╗  ██╗██╗    ██████╗  █████╗ ██████╗      ██████╗███████╗ ██████╗
// ██╔══██╗╚██╗██╔╝██║    ██╔══██╗██╔══██╗██╔══██╗    ██╔════╝██╔════╝██╔════╝
// ███████║ ╚███╔╝ ██║    ██████╔╝███████║██████╔╝    ██║     █████╗  ██║  ███╗
// ██╔══██║ ██╔██╗ ██║    ██╔══██╗██╔══██║██╔══██╗    ██║     ██╔══╝  ██║   ██║
// ██║  ██║██╔╝ ██╗██║    ██║  ██║██║  ██║██████╔╝    ╚██████╗██║     ╚██████╔╝
// ╚═╝  ╚═╝╚═╝  ╚═╝╚═╝    ╚═╝  ╚═╝╚═╝  ╚═╝╚═════╝      ╚═════╝╚═╝      ╚═════╝
//
//
// Author: Pirmin Vogel - vogelpi@iis.ee.ethz.ch
//
// Purpose : AXI4-Lite configuration and miss handling interface for RAB
//
// --=========================================================================--

module axi_rab_cfg
  #(
    parameter N_PORTS         =   3,
    parameter N_REGS          = 196,
    parameter N_SLICES_TOT    =  48,
    parameter N_L2_SETS       =  32,
    parameter N_L2_SET_ENTRIES=  32,
    parameter ADDR_WIDTH_PHYS =  40,
    parameter ADDR_WIDTH_VIRT =  32,
    parameter N_FLAGS         =   4,
    parameter AXI_DATA_WIDTH  =  64,
    parameter AXI_ADDR_WIDTH  =  32,
    parameter MISS_META_WIDTH =  10,  // <= FIFO_WIDTH
    parameter MH_FIFO_DEPTH   =  16
    )
   (
    input  logic                                    Clk_CI,
    input  logic                                    Rst_RBI,

    // AXI Lite interface
    input  logic [AXI_ADDR_WIDTH-1:0]               s_axi_awaddr,
    input  logic                                    s_axi_awvalid,
    output logic                                    s_axi_awready,
    input  logic [AXI_DATA_WIDTH/8-1:0][7:0]        s_axi_wdata,
    input  logic [AXI_DATA_WIDTH/8-1:0]             s_axi_wstrb,
    input  logic                                    s_axi_wvalid,
    output logic                                    s_axi_wready,
    output logic [1:0]                              s_axi_bresp,
    output logic                                    s_axi_bvalid,
    input  logic                                    s_axi_bready,
    input  logic [AXI_ADDR_WIDTH-1:0]               s_axi_araddr,
    input  logic                                    s_axi_arvalid,
    output logic                                    s_axi_arready,
    output logic [AXI_DATA_WIDTH-1:0]               s_axi_rdata,
    output logic [1:0]                              s_axi_rresp,
    output logic                                    s_axi_rvalid,
    input  logic                                    s_axi_rready,

    // Slice configuration
    output logic [N_REGS-1:0][63:0]                 L1Cfg_DO,
    output logic                                    L1AllowMultiHit_SO,

    // Miss handling
    input  logic [ADDR_WIDTH_VIRT-1:0]              MissAddr_DI,
    input  logic [MISS_META_WIDTH-1:0]              MissMeta_DI,
    input  logic                                    Miss_SI,
    output logic                                    MhFifoFull_SO,

    // L2 TLB
    output logic [N_PORTS-1:0] [AXI_DATA_WIDTH-1:0] wdata_l2,
    output logic [N_PORTS-1:0] [AXI_ADDR_WIDTH-1:0] waddr_l2,
    output logic [N_PORTS-1:0]                      wren_l2,

    // Invalidation
    input logic                                     l1_invalidate_ready_i,
    input logic  [N_SLICES_TOT-1:0]                 l1_invalidate_slices_i,
    input logic  [N_PORTS-1:0]                      l2_invalidate_done_i,
    output logic [ADDR_WIDTH_VIRT-1:0]              invalidate_addr_min_o,
    output logic [ADDR_WIDTH_VIRT-1:0]              invalidate_addr_max_o,
    output logic                                    invalidate_addr_valid_o
  );

  localparam ADDR_LSB = $clog2(64/8); // 64 even if the AXI Lite interface is 32,
                                      // because RAB slices are 64 bit wide.
  localparam ADDR_MSB = $clog2(N_REGS)+ADDR_LSB-1;

  localparam CONFIG_SIZE = 'h20; // Addresses at start to use for config registers
  localparam L2SINGLE_AMAP_SIZE = 16'h4000; // Maximum 2048 TLB entries in L2

  localparam integer N_L2_ENTRIES = N_L2_SETS * N_L2_SET_ENTRIES;

  localparam logic [AXI_ADDR_WIDTH-1:0] L2_VA_MAX_ADDR = (N_L2_ENTRIES-1) << 2;

  logic [AXI_DATA_WIDTH/8-1:0][7:0] L1Cfg_DP[N_REGS]; // [Byte][Bit]
  logic                             WriteConfigDisabled;
  genvar j;

  //  █████╗ ██╗  ██╗██╗██╗  ██╗      ██╗     ██╗████████╗███████╗
  // ██╔══██╗╚██╗██╔╝██║██║  ██║      ██║     ██║╚══██╔══╝██╔════╝
  // ███████║ ╚███╔╝ ██║███████║█████╗██║     ██║   ██║   █████╗
  // ██╔══██║ ██╔██╗ ██║╚════██║╚════╝██║     ██║   ██║   ██╔══╝
  // ██║  ██║██╔╝ ██╗██║     ██║      ███████╗██║   ██║   ███████╗
  // ╚═╝  ╚═╝╚═╝  ╚═╝╚═╝     ╚═╝      ╚══════╝╚═╝   ╚═╝   ╚══════╝
  //
  logic [AXI_ADDR_WIDTH-1:0]        awaddr_reg;
  logic                             awaddr_done_rise;
  logic                             awaddr_done_reg;
  logic                             awaddr_done_reg_dly;

  logic [AXI_DATA_WIDTH/8-1:0][7:0] wdata_reg;
  logic [AXI_DATA_WIDTH/8-1:0]      wstrb_reg;
  logic                             wdata_done_rise;
  logic                             wdata_done_reg;
  logic                             wdata_done_reg_dly;

  logic                             wresp_done_reg;
  logic                             wresp_running_reg;
  logic                             wresp_block;

  logic [AXI_ADDR_WIDTH-1:0]        araddr_reg;
  logic                             araddr_done_reg;

  logic [AXI_DATA_WIDTH-1:0]        rdata_reg;
  logic                             rresp_done_reg;
  logic                             rresp_running_reg;

  logic                             awready;
  logic                             wready;
  logic                             bvalid;
  logic [1:0]                       bresp;

  logic                             arready;
  logic                             rvalid;

  logic                             wren;
  logic                             wrvalid;

  assign wren = ( wdata_done_rise & awaddr_done_reg ) | ( awaddr_done_rise & wdata_done_reg );
  assign wdata_done_rise  = wdata_done_reg  & ~wdata_done_reg_dly;
  assign awaddr_done_rise = awaddr_done_reg & ~awaddr_done_reg_dly;

  // reg_dly
  always @(posedge Clk_CI or negedge Rst_RBI)
    begin
       if (!Rst_RBI)
         begin
            wdata_done_reg_dly  <= 1'b0;
            awaddr_done_reg_dly <= 1'b0;
         end
       else
         begin
            wdata_done_reg_dly  <= wdata_done_reg;
            awaddr_done_reg_dly <= awaddr_done_reg;
         end
    end

  // AW Channel
  always @(posedge Clk_CI or negedge Rst_RBI)
    begin
       if (!Rst_RBI)
         begin
            awaddr_done_reg <= 1'b0;
            awaddr_reg      <= '0;
            awready         <= 1'b1;
         end
       else
         begin
            if (awready && s_axi_awvalid)
              begin
                 awready         <= 1'b0;
                 awaddr_done_reg <= 1'b1;
                 awaddr_reg      <= s_axi_awaddr;
              end
            else if (awaddr_done_reg && wresp_done_reg)
              begin
                 awready         <= 1'b1;
                 awaddr_done_reg <= 1'b0;
              end
         end
    end

  // W Channel
  always @(posedge Clk_CI or negedge Rst_RBI)
    begin
       if (!Rst_RBI)
         begin
            wdata_done_reg <= 1'b0;
            wready         <= 1'b1;
            wdata_reg      <= '0;
            wstrb_reg      <= '0;
         end
       else
         begin
            if (wready && s_axi_wvalid)
              begin
                 wready         <= 1'b0;
                 wdata_done_reg <= 1'b1;
                 wdata_reg      <= s_axi_wdata;
                 wstrb_reg      <= s_axi_wstrb;
              end
            else if (wdata_done_reg && wresp_done_reg)
              begin
                 wready         <= 1'b1;
                 wdata_done_reg <= 1'b0;
              end
         end
    end

  // B Channel
  always @(posedge Clk_CI or negedge Rst_RBI)
    begin
       if (!Rst_RBI)
         begin
            bvalid            <= 1'b0;
            bresp             <= 2'b00;
            wresp_done_reg    <= 1'b0;
            wresp_running_reg <= 1'b0;
         end
       else
         begin
            if (awaddr_done_reg && wdata_done_reg && !wresp_done_reg && !wresp_block)
              begin
                 if (!wresp_running_reg)
                   begin
                      bvalid            <= 1'b1;
                      if (wrvalid)
                        bresp           <= 2'b00;
                      else
                        bresp           <= 2'b10;
                      wresp_running_reg <= 1'b1;
                   end
                 else if (s_axi_bready)
                   begin
                      bvalid            <= 1'b0;
                      bresp             <= 2'b00;
                      wresp_done_reg    <= 1'b1;
                      wresp_running_reg <= 1'b0;
                   end
              end
            else
              begin
                 bvalid            <= 1'b0;
                 bresp             <= 2'b00;
                 wresp_done_reg    <= 1'b0;
                 wresp_running_reg <= 1'b0;
              end
         end
    end

  // AR Channel
  always @(posedge Clk_CI or negedge Rst_RBI)
    begin
       if (!Rst_RBI)
         begin
            araddr_done_reg <= 1'b0;
            arready         <= 1'b1;
            araddr_reg       <= '0;
         end
       else
         begin
            if (arready && s_axi_arvalid)
              begin
                 arready         <= 1'b0;
                 araddr_done_reg <= 1'b1;
                 araddr_reg      <= s_axi_araddr;
              end
            else if (araddr_done_reg && rresp_done_reg)
              begin
                 arready         <= 1'b1;
                 araddr_done_reg <= 1'b0;
              end
         end
    end

  // R Channel
  always @(posedge Clk_CI or negedge Rst_RBI)
    begin
       if (!Rst_RBI)
         begin
            rresp_done_reg    <= 1'b0;
            rvalid            <= 1'b0;
            rresp_running_reg <= 1'b0;
         end
       else
         begin
            if (araddr_done_reg && !rresp_done_reg)
              begin
                 if (!rresp_running_reg)
                   begin
                      rvalid            <= 1'b1;
                      rresp_running_reg <= 1'b1;
                   end
                 else if (s_axi_rready)
                   begin
                      rvalid            <= 1'b0;
                      rresp_done_reg    <= 1'b1;
                      rresp_running_reg <= 1'b0;
                   end
              end
            else
              begin
                 rvalid            <= 1'b0;
                 rresp_done_reg    <= 1'b0;
                 rresp_running_reg <= 1'b0;
              end
         end
    end

  assign s_axi_awready = awready;
  assign s_axi_wready  = wready;

  assign s_axi_bresp   = bresp;
  assign s_axi_bvalid  = bvalid;

  assign s_axi_arready = arready;
  assign s_axi_rresp   = 2'b00;
  assign s_axi_rvalid  = rvalid;

  // ██╗     ██╗     ██████╗███████╗ ██████╗     ██████╗ ███████╗ ██████╗
  // ██║    ███║    ██╔════╝██╔════╝██╔════╝     ██╔══██╗██╔════╝██╔════╝
  // ██║    ╚██║    ██║     █████╗  ██║  ███╗    ██████╔╝█████╗  ██║  ███╗
  // ██║     ██║    ██║     ██╔══╝  ██║   ██║    ██╔══██╗██╔══╝  ██║   ██║
  // ███████╗██║    ╚██████╗██║     ╚██████╔╝    ██║  ██║███████╗╚██████╔╝
  // ╚══════╝╚═╝     ╚═════╝╚═╝      ╚═════╝     ╚═╝  ╚═╝╚══════╝ ╚═════╝
  //
  logic invalidate_in_progress_q, invalidate_in_progress_d;

  logic wren_l1;
  assign wren_l1 = wren && (CONFIG_SIZE <= awaddr_reg) && (awaddr_reg < L2SINGLE_AMAP_SIZE);

  always @( posedge Clk_CI or negedge Rst_RBI )
    begin
      var integer idx_reg, idx_byte, idx_slice;
      if ( Rst_RBI == 1'b0 )
        begin
          for ( idx_reg = 0; idx_reg < N_REGS; idx_reg++ )
            L1Cfg_DP[idx_reg] <= '0;
        end
      else if ( invalidate_in_progress_q && l1_invalidate_ready_i )
        begin
           for ( idx_slice = 0; idx_slice < N_SLICES_TOT; ++idx_slice ) begin
              if ( l1_invalidate_slices_i[idx_slice] ) begin
                 L1Cfg_DP[4*idx_slice+7] <= 'h0; // disable the slice that hit
              end
           end
        end
      else if ( wren_l1 & wrvalid )
          begin
            if ( awaddr_reg[ADDR_LSB+1] == 1'b0 ) begin                     // VIRT_ADDR
              for ( idx_byte = 0; idx_byte < AXI_DATA_WIDTH/8; idx_byte++ ) begin
                if ( (idx_byte < ADDR_WIDTH_VIRT/8) ) begin
                  if ( wstrb_reg[idx_byte] ) begin
                    L1Cfg_DP[awaddr_reg[ADDR_MSB:ADDR_LSB]][idx_byte] <= wdata_reg[idx_byte];
                  end
                end
                else begin  // Let synthesizer optimize away unused registers.
                  L1Cfg_DP[awaddr_reg[ADDR_MSB:ADDR_LSB]][idx_byte] <= '0;
                end
              end
            end
            else if ( awaddr_reg[ADDR_LSB+1:ADDR_LSB] == 2'b10 ) begin      // PHYS_ADDR
              for ( idx_byte = 0; idx_byte < AXI_DATA_WIDTH/8; idx_byte++ ) begin
                if ( (idx_byte < ADDR_WIDTH_PHYS/8) ) begin
                  if ( wstrb_reg[idx_byte] ) begin
                    L1Cfg_DP[awaddr_reg[ADDR_MSB:ADDR_LSB]][idx_byte] <= wdata_reg[idx_byte];
                  end
                end
                else begin  // Let synthesizer optimize away unused registers.
                  L1Cfg_DP[awaddr_reg[ADDR_MSB:ADDR_LSB]][idx_byte] <= '0;
                end
              end
            end
            else begin // ( awaddr_reg[ADDR_LSB+1:ADDR_LSB] == 2'b11 )      // FLAGS
              for ( idx_byte = 0; idx_byte < AXI_DATA_WIDTH/8; idx_byte++ ) begin
                if ( (idx_byte < 1) ) begin
                  if ( wstrb_reg[idx_byte] ) begin
                    L1Cfg_DP[awaddr_reg[ADDR_MSB:ADDR_LSB]][idx_byte] <= wdata_reg[idx_byte] & { {{8-N_FLAGS}{1'b0}}, {{N_FLAGS}{1'b1}} };
                  end
                end
                else begin  // Let synthesizer optimize away unused registers.
                  L1Cfg_DP[awaddr_reg[ADDR_MSB:ADDR_LSB]][idx_byte] <= '0;
                end
              end
            end
          end
    end // always @ ( posedge Clk_CI or negedge Rst_RBI )

  generate
    // Mask unused bits -> Synthesizer should optimize away unused registers
    for( j=0; j<N_REGS; j++ ) begin
      if ( j[1] == 1'b0 ) // VIRT_ADDR
        assign L1Cfg_DO[j] = { {{64-ADDR_WIDTH_VIRT}{1'b0}},{ADDR_WIDTH_VIRT{1'b1}} } & L1Cfg_DP[j];
      else if ( j[1:0] == 2'b10 ) // PHYS_ADDR
        assign L1Cfg_DO[j] = { {{64-ADDR_WIDTH_PHYS}{1'b0}},{ADDR_WIDTH_PHYS{1'b1}} } & L1Cfg_DP[j];
      else // if ( j[1:0] == 2'b11 ) // FLAGS
        assign L1Cfg_DO[j] = { {{64-N_FLAGS}{1'b0}},{N_FLAGS{1'b1}} } & L1Cfg_DP[j];
    end
  endgenerate

  always_comb
    begin
      if ( araddr_reg[ADDR_LSB-1] == 1'b1 ) // read upper 32 bit, for debugging over 32-bit interface
        rdata_reg = { {32'h00000000},{L1Cfg_DO[araddr_reg[ADDR_MSB:ADDR_LSB]][63:32]} };
      else
        rdata_reg = L1Cfg_DO[araddr_reg[ADDR_MSB:ADDR_LSB]];
    end

  // ██╗     ██████╗      ██████╗███████╗ ██████╗
  // ██║     ╚════██╗    ██╔════╝██╔════╝██╔════╝
  // ██║      █████╔╝    ██║     █████╗  ██║  ███╗
  // ██║     ██╔═══╝     ██║     ██╔══╝  ██║   ██║
  // ███████╗███████╗    ╚██████╗██║     ╚██████╔╝
  // ╚══════╝╚══════╝     ╚═════╝╚═╝      ╚═════╝
  //
  logic [N_PORTS-1:0] l2_addr_is_in_va_rams;
  logic [N_PORTS-1:0] upper_word_is_written;
  logic [N_PORTS-1:0] lower_word_is_written;
  generate
    for( j=0; j< N_PORTS; j++)
      begin
        if (AXI_DATA_WIDTH == 64) begin
          assign l2_addr_is_in_va_rams[j] = (awaddr_reg >= (j+1)*L2SINGLE_AMAP_SIZE) && (awaddr_reg[$clog2(L2SINGLE_AMAP_SIZE)-1:0] <= L2_VA_MAX_ADDR);
          assign upper_word_is_written[j] = (wstrb_reg[7:4] != 4'b0000);
          assign lower_word_is_written[j] = (wstrb_reg[3:0] != 4'b0000);
        end else begin
          assign l2_addr_is_in_va_rams[j] = 1'b0;
          assign upper_word_is_written[j] = 1'b0;
          assign lower_word_is_written[j] = 1'b0;
        end

        always @( posedge Clk_CI or negedge Rst_RBI ) begin
          var integer idx_byte, off_byte;
          if ( Rst_RBI == 1'b0 )
            begin
              wren_l2[j]  <= 1'b0;
              wdata_l2[j] <= '0;
            end
          else if (wren & wrvalid)
            begin
              if ( (awaddr_reg >= (j+1)*L2SINGLE_AMAP_SIZE) && (awaddr_reg < (j+2)*L2SINGLE_AMAP_SIZE) && (|wstrb_reg) )
                wren_l2[j] <= 1'b1;
              if      (AXI_DATA_WIDTH == 32) begin
                for ( idx_byte = 0; idx_byte < AXI_DATA_WIDTH/8; idx_byte++ )
                  wdata_l2[j][idx_byte*8 +: 8] <= wdata_reg[idx_byte] & {8{wstrb_reg[idx_byte]}};
              end
              else if (AXI_DATA_WIDTH == 64) begin
                if (lower_word_is_written[j] == 1'b1)
                  off_byte = 0;
                else
                  off_byte = 4;
                // always put the payload in the lower word and set upper word to 0
                for ( idx_byte = 0; idx_byte < AXI_DATA_WIDTH/8/2; idx_byte++ )
                    wdata_l2[j][idx_byte*8 +: 8] <= wdata_reg[idx_byte+off_byte] & {8{wstrb_reg[idx_byte+off_byte]}};
                wdata_l2[j][AXI_DATA_WIDTH-1:AXI_DATA_WIDTH/2] <= 'b0;
              end
              // pragma translate_off
              else
                $fatal(1, "Unsupported AXI_DATA_WIDTH!");
              // pragma translate_on
            end
          else
            wren_l2[j] <= '0;
        end // always @ ( posedge Clk_CI or negedge Rst_RBI )

        // Properly align the 32-bit word address when writing from 64-bit interface:
        // Depending on the system, the incoming address is (non-)aligned to the 64-bit
        // word when writing the upper 32-bit word.
        always_comb begin
          waddr_l2[j] = (awaddr_reg -(j+1)*L2SINGLE_AMAP_SIZE)/4;
          if (wren_l2[j]) begin
            if (AXI_DATA_WIDTH == 64) begin
              if (upper_word_is_written[j] == 1'b1) begin
                // address must be non-aligned
                waddr_l2[j][0] = 1'b1;
              end
            end
            // pragma translate_off
            else if (AXI_DATA_WIDTH != 32) begin
              $fatal(1, "Unsupported AXI_DATA_WIDTH!");
            end
            // pragma translate_on
          end
        end

        // Assert that only one 32-bit word is ever written at a time to VA RAMs on 64-bit data
        // systems.
        // pragma translate_off
        always_ff @ (posedge Clk_CI) begin
          if (AXI_DATA_WIDTH == 64) begin
            if  (l2_addr_is_in_va_rams[j]) begin
              if (upper_word_is_written[j]) begin
                assert (!lower_word_is_written[j])
                  else $error("Unsupported write across two 32-bit words to VA RAMs!");
              end
              else if (lower_word_is_written[j]) begin
                assert (!upper_word_is_written[j])
                  else $error("Unsupported write across two 32-bit words to VA RAMs!");
              end
            end
          end
        end
        // pragma translate_on

      end // for (j=0; j< N_PORTS; j++)
   endgenerate

  // ███╗   ███╗██╗  ██╗    ███████╗██╗███████╗ ██████╗ ███████╗
  // ████╗ ████║██║  ██║    ██╔════╝██║██╔════╝██╔═══██╗██╔════╝
  // ██╔████╔██║███████║    █████╗  ██║█████╗  ██║   ██║███████╗
  // ██║╚██╔╝██║██╔══██║    ██╔══╝  ██║██╔══╝  ██║   ██║╚════██║
  // ██║ ╚═╝ ██║██║  ██║    ██║     ██║██║     ╚██████╔╝███████║
  // ╚═╝     ╚═╝╚═╝  ╚═╝    ╚═╝     ╚═╝╚═╝      ╚═════╝ ╚══════╝
  //
  logic [ADDR_WIDTH_VIRT-1:0] AddrFifoDin_D;
  logic                       AddrFifoWen_S;
  logic                       AddrFifoRen_S;
  logic [ADDR_WIDTH_VIRT-1:0] AddrFifoDout_D;
  logic                       AddrFifoFull_S;
  logic                       AddrFifoEmpty_S;
  logic                       AddrFifoEmpty_SB;
  logic                       AddrFifoFull_SB;

  logic [MISS_META_WIDTH-1:0] MetaFifoDin_D;
  logic                       MetaFifoWen_S;
  logic                       MetaFifoRen_S;
  logic [MISS_META_WIDTH-1:0] MetaFifoDout_D;
  logic                       MetaFifoFull_S;
  logic                       MetaFifoEmpty_S;
  logic                       MetaFifoEmpty_SB;
  logic                       MetaFifoFull_SB;

  logic                       FifosDisabled_S;
  logic                       ConfRegWen_S;
  logic [2:0]                 ConfReg_DN;
  logic [2:0]                 ConfReg_DP;

  logic [AXI_DATA_WIDTH-1:0]  wdata_reg_vec;

  logic                       wren_config;

  assign FifosDisabled_S     = ConfReg_DP[0];
  assign L1AllowMultiHit_SO  = ConfReg_DP[1];
  assign WriteConfigDisabled = ConfReg_DP[2];

  assign AddrFifoEmpty_S = ~AddrFifoEmpty_SB;
  assign MetaFifoEmpty_S = ~MetaFifoEmpty_SB;

  assign AddrFifoFull_S = ~AddrFifoFull_SB;
  assign MetaFifoFull_S = ~MetaFifoFull_SB;

  assign MhFifoFull_SO = (AddrFifoWen_S & AddrFifoFull_S) | (MetaFifoWen_S & MetaFifoFull_S);

  generate
     for ( j=0; j<AXI_DATA_WIDTH/8; j++ )
       assign wdata_reg_vec[(j+1)*8-1:j*8] = wdata_reg[j];
  endgenerate

  assign wren_config = wren && (awaddr_reg < CONFIG_SIZE);

  // check if write to address was valid (NOTE: wren check only works for non-blocked responses)
  assign wrvalid = !wren | (wren & (wren_config | !WriteConfigDisabled));

  // write address FIFO
  always_comb
    begin
       AddrFifoWen_S = 1'b0;
       AddrFifoDin_D = 'b0;
       if ( (Miss_SI == 1'b1) && (FifosDisabled_S == 1'b0) ) // register a new miss
         begin
            AddrFifoWen_S = 1'b1;
            AddrFifoDin_D = MissAddr_DI;
         end
       else if ( (wren_config == 1'b1) && (awaddr_reg[ADDR_MSB:0] == 'b0) && (FifosDisabled_S == 1'b0)) // write request from AXI interface
         begin
            AddrFifoWen_S = 1'b1;
            AddrFifoDin_D = wdata_reg_vec[ADDR_WIDTH_VIRT-1:0];
         end
    end

  // write meta FIFO
  always_comb
    begin
       MetaFifoWen_S = 1'b0;
       MetaFifoDin_D = 'b0;
       if ( (Miss_SI == 1'b1) && (FifosDisabled_S == 1'b0) ) // register a new miss
         begin
            MetaFifoWen_S                      = 1'b1;
            MetaFifoDin_D[MISS_META_WIDTH-1:0] = MissMeta_DI;
         end
       else if ( (wren_config == 1'b1) && (awaddr_reg[ADDR_MSB:0] == 4'h8) && (FifosDisabled_S == 1'b0) ) // write request from AXI interface
         begin
            MetaFifoWen_S = 1'b1;
            MetaFifoDin_D = wdata_reg_vec[MISS_META_WIDTH-1:0];
         end
    end

  // write configuration register
  always_comb
    begin
       ConfRegWen_S = 1'b0;
       ConfReg_DN   = 1'b0;
       if ( (wren_config == 1'b1) && (awaddr_reg[ADDR_MSB:0] == 4'hC) ) // write request from AXI interface
         begin
            ConfRegWen_S = 1'b1;
            ConfReg_DN   = wdata_reg_vec[$high(ConfReg_DN):0];
         end
    end

  // AXI read data
  always_comb
    begin
       s_axi_rdata   = rdata_reg; // read L1 config
       AddrFifoRen_S = 1'b0;
       MetaFifoRen_S = 1'b0;
       if ( rvalid == 1'b1 )
         begin
            // read address FIFO
            if ( araddr_reg[ADDR_MSB:0] == 'b0 )
              begin
                s_axi_rdata                      = {AXI_DATA_WIDTH{1'b0}};
                s_axi_rdata[ADDR_WIDTH_VIRT-1:0] = AddrFifoDout_D;
                if ( AddrFifoEmpty_S == 1'b0 )
                  AddrFifoRen_S = 1'b1;
              end
            // read meta FIFO
            else if ( araddr_reg[ADDR_MSB:0] == 4'h8 )
              begin
                s_axi_rdata                      = {AXI_DATA_WIDTH{1'b0}};
                s_axi_rdata[31]                  = MetaFifoEmpty_S;
                s_axi_rdata[MISS_META_WIDTH-1:0] = MetaFifoDout_D;
                if ( MetaFifoEmpty_S == 1'b0 )
                  MetaFifoRen_S = 1'b1;
              end
            // read configuration register
            else if ( araddr_reg[ADDR_MSB:0] == 4'hC )
              begin
                s_axi_rdata                      = {AXI_DATA_WIDTH{1'b0}};
                s_axi_rdata[$high(ConfReg_DP):0] = ConfReg_DP;
              end
         end // if ( rvalid == 1'b1 )
    end // always_comb begin

  // configuration register
  always_ff @(posedge Clk_CI or negedge Rst_RBI) begin
    if (Rst_RBI == 1'b0)
      begin
        ConfReg_DP <= 'b0;
      end
    else if (ConfRegWen_S == 1'b1)
      begin
        ConfReg_DP <= ConfReg_DN;
      end
  end

  generic_fifo
    #(
      .DATA_WIDTH ( ADDR_WIDTH_VIRT ),
      .DATA_DEPTH ( MH_FIFO_DEPTH   )
      )
    fifo_addr_i
    (
      .clk         ( Clk_CI                          ),
      .rst_n       ( Rst_RBI                         ),
      .data_i      ( AddrFifoDin_D                   ),
      .valid_i     ( AddrFifoWen_S & AddrFifoFull_SB ),
      .grant_o     ( AddrFifoFull_SB                 ),
      .data_o      ( AddrFifoDout_D                  ),
      .valid_o     ( AddrFifoEmpty_SB                ),
      .grant_i     ( AddrFifoRen_S                   ),
      .test_mode_i ( 1'b0                            )
    );

  generic_fifo
    #(
      .DATA_WIDTH ( MISS_META_WIDTH ),
      .DATA_DEPTH ( MH_FIFO_DEPTH   )
      )
    fifo_meta_i
    (
      .clk         ( Clk_CI                          ),
      .rst_n       ( Rst_RBI                         ),
      .data_i      ( MetaFifoDin_D                   ),
      .valid_i     ( MetaFifoWen_S & MetaFifoFull_SB ),
      .grant_o     ( MetaFifoFull_SB                 ),
      .data_o      ( MetaFifoDout_D                  ),
      .valid_o     ( MetaFifoEmpty_SB                ),
      .grant_i     ( MetaFifoRen_S                   ),
      .test_mode_i ( 1'b0                            )
    );


  //
  // INVALIDATE
  //

  logic                       l1_invalidate_done_q, l1_invalidate_done_d;
  logic [N_PORTS-1:0]         l2_invalidate_done_q, l2_invalidate_done_d;
  logic [ADDR_WIDTH_VIRT-1:0] invalidate_addr_min_q;
  logic [ADDR_WIDTH_VIRT-1:0] invalidate_addr_min_d;
  logic [ADDR_WIDTH_VIRT-1:0] invalidate_addr_max_q;
  logic [ADDR_WIDTH_VIRT-1:0] invalidate_addr_max_d;

  assign wresp_block = invalidate_in_progress_q || invalidate_in_progress_d; // FIXME: should this be set at the beginning
  assign invalidate_addr_min_o = invalidate_addr_min_q;
  assign invalidate_addr_max_o = invalidate_addr_max_q;
  assign invalidate_addr_valid_o = invalidate_in_progress_q;

  // write start invalidate register
  always_comb begin
     invalidate_addr_min_d = invalidate_addr_min_q;
     if ( (wren_config == 'b1) && (awaddr_reg[ADDR_MSB:0] == 8'h10) && !invalidate_in_progress_q) begin
        invalidate_addr_min_d = wdata_reg_vec[ADDR_WIDTH_VIRT-1:0];
     end
  end
  // write end invalidate register (NOTE: blocks until invalidation is completed)
  always_comb begin
     invalidate_addr_max_d = invalidate_addr_max_q;
     invalidate_in_progress_d = invalidate_in_progress_q;
     if ((wren_config == 'b1) && (awaddr_reg[ADDR_MSB:0] == 8'h18) && !invalidate_in_progress_q) begin
        invalidate_addr_max_d = wdata_reg_vec[ADDR_WIDTH_VIRT-1:0];
        invalidate_in_progress_d = 'b1;
     end else if (l1_invalidate_done_q && (&l2_invalidate_done_q)) begin
        invalidate_in_progress_d = 'b0;
     end
  end

  // handle invalidation of l1 registers that are hit
  always_comb begin
     l1_invalidate_done_d = l1_invalidate_done_q;
     if (invalidate_in_progress_q && l1_invalidate_ready_i) begin
        // NOTE: the actual invalidation will happen in the same cycle in the L1 config logic
        l1_invalidate_done_d = 'b1;
     end else if (!invalidate_in_progress_q) begin
        l1_invalidate_done_d = 'b0;
     end
  end

  // check if every l2 is finished invalidating
  generate for (j = 0; j < N_PORTS; ++j) begin
    always_comb begin
      l2_invalidate_done_d[j] = l2_invalidate_done_q[j];
      if (invalidate_in_progress_q && l2_invalidate_done_i[j]) begin
        l2_invalidate_done_d[j] = 'b1;
      end else if (!invalidate_in_progress_q) begin
        l2_invalidate_done_d[j] = 'b0;
      end
    end
  end
  endgenerate

  // store invalidation registers
  always_ff @(posedge Clk_CI or negedge Rst_RBI) begin
     if (Rst_RBI == 'b0) begin
        invalidate_addr_min_q <= 'b0;
        invalidate_addr_max_q <= 'b0;
        invalidate_in_progress_q <= 'b0;
        l1_invalidate_done_q <= 'b0;
        l2_invalidate_done_q <= 'b0;
     end else begin
        invalidate_addr_min_q <= invalidate_addr_min_d;
        invalidate_addr_max_q <= invalidate_addr_max_d;
        invalidate_in_progress_q <= invalidate_in_progress_d;
        l1_invalidate_done_q <= l1_invalidate_done_d;
        l2_invalidate_done_q <= l2_invalidate_done_d;
     end
  end

endmodule

// vim: ts=2 sw=2 sts=2 et nosmartindent autoindent foldmethod=marker
