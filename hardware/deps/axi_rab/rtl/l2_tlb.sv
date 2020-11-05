// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

//`define MULTI_HIT_FULL_SET  // Enable full multi hit detection. Always the entire set is searched.
//`define MULTI_HIT_CUR_CYCLE // Enable partial multi hit detection. Only multi hits in the same search cycle are detected.

`ifdef MULTI_HIT_FULL_SET
  `ifndef MULTI_HIT_CUR_CYCLE
    `define MULTI_HIT_CUR_CYCLE
  `endif
`endif

module l2_tlb
  #(
    parameter AXI_S_ADDR_WIDTH       = 32,
    parameter AXI_M_ADDR_WIDTH       = 40,
    parameter AXI_LITE_DATA_WIDTH    = 64,
    parameter AXI_LITE_ADDR_WIDTH    = 32,
    parameter N_SETS                 = 32,
    parameter N_OFFSETS              = 4, //per port. There are 2 ports.
    parameter PAGE_SIZE              = 4096, // 4kB
    parameter N_PAR_VA_RAMS          = 4,
    parameter HIT_OFFSET_STORE_WIDTH = 2 // Num of bits of VA RAM offset stored. This should not be greater than OFFSET_WIDTH
    )
   (
    input  logic                           clk_i,
    input  logic                           rst_ni,

    input  logic                           we_i,
    input  logic [AXI_LITE_ADDR_WIDTH-1:0] waddr_i,
    input  logic [AXI_LITE_DATA_WIDTH-1:0] wdata_i,

    input  logic                           start_i,
    output logic                           busy_o,
    input  logic    [AXI_S_ADDR_WIDTH-1:0] in_addr_min_i,
    input  logic    [AXI_S_ADDR_WIDTH-1:0] in_addr_max_i, // required not to cross any page boundary unless invalidate mode is on
    input  logic                           rw_type_i, //1 => write, 0=> read
    input  logic                           invalidate_i,

    input  logic                           out_ready_i,
    output logic                           out_valid_o,
    output logic                           hit_o,
    output logic                           miss_o,
    output logic                           prot_o,
    output logic                           multi_o,
    output logic                           cache_coherent_o,
    output logic    [AXI_M_ADDR_WIDTH-1:0] out_addr_o
    );

   localparam VA_RAM_DEPTH      = N_SETS * N_OFFSETS * 2;
   localparam PA_RAM_DEPTH      = VA_RAM_DEPTH * N_PAR_VA_RAMS;
   localparam VA_RAM_ADDR_WIDTH = $clog2(VA_RAM_DEPTH);
   localparam PA_RAM_ADDR_WIDTH = $clog2(PA_RAM_DEPTH);
   localparam SET_WIDTH         = $clog2(N_SETS);
   localparam OFFSET_WIDTH      = $clog2(N_OFFSETS);
   localparam LL_WIDTH          = $clog2(N_PAR_VA_RAMS);
   localparam IGNORE_LSB        = $clog2(PAGE_SIZE);

   localparam VA_RAM_DATA_WIDTH = AXI_S_ADDR_WIDTH - IGNORE_LSB + 4;
   localparam PA_RAM_DATA_WIDTH = AXI_M_ADDR_WIDTH - IGNORE_LSB;

   logic                               [N_PAR_VA_RAMS-1:0] hit, prot, multi_hit, cache_coherent;
   logic                               [N_PAR_VA_RAMS-1:0] ram_we;
   logic                                                   last_search, last_search_next;
   logic                                                   first_search, first_search_next;
   logic                                                   first_set, first_set_next;
   logic [N_PAR_VA_RAMS-1:0][SET_WIDTH+OFFSET_WIDTH+1-1:0] ram_waddr;
   logic                           [VA_RAM_DATA_WIDTH-1:0] ram_wdata;
   logic [N_PAR_VA_RAMS-1:0][SET_WIDTH+OFFSET_WIDTH+1-1:0] hit_addr;
   logic                                                   pa_ram_we;
   logic                           [PA_RAM_ADDR_WIDTH-1:0] pa_port0_raddr, pa_port0_waddr; // PA RAM read, Write addr;
   logic                           [PA_RAM_ADDR_WIDTH-1:0] pa_port0_raddr_reg_SN, pa_port0_raddr_reg_SP; // registered addresses, needed for WAIT_ON_WRITE;
   logic                           [PA_RAM_ADDR_WIDTH-1:0] pa_port0_addr; // PA RAM addr
   logic                           [PA_RAM_DATA_WIDTH-1:0] pa_port0_data, pa_data, pa_port0_data_reg; // PA RAM data
   logic                                                   pa_ram_store_data_SN, pa_ram_store_data_SP;
   logic                                                   hit_top, prot_top, multi_hit_top, first_hit_top;
   logic                                                   output_sent;
   int                                                     hit_block_num;

   logic                                                   searching, search_done;
   logic                    [SET_WIDTH+OFFSET_WIDTH+1-1:0] port0_raddr;
   logic [N_PAR_VA_RAMS-1:0][SET_WIDTH+OFFSET_WIDTH+1-1:0] port0_addr; // VA RAM port0 addr
   logic                    [SET_WIDTH+OFFSET_WIDTH+1-1:0] port1_addr; // VA RAM port1 addr
   logic                                [OFFSET_WIDTH-1:0] offset_addr, offset_addr_d;
   logic                                [OFFSET_WIDTH-1:0] offset_start_addr, offset_end_addr;
   logic                                   [SET_WIDTH-1:0] set_num_q, set_num_d;
   logic                                   [SET_WIDTH-1:0] set_num, min_set_num, max_set_num;
   logic                                                   rollback;

   logic                                                   va_output_valid;
   logic                                                   searching_q;

   genvar                                                  z;

   // Search FSM
   typedef enum logic                                [1:0] {IDLE, SEARCH, DONE} search_state_t;
   search_state_t                                          search_SP; // Present state
   search_state_t                                          search_SN; // Next State

   // Output FSM
   typedef enum logic                                [1:0] {OUT_IDLE, SEND_OUTPUT, WAIT_ON_WRITE} out_state_t;
   out_state_t                                             out_SP; // Present state
   out_state_t                                             out_SN; // Next State

   logic                                                   miss_next;
   logic                                                   hit_next;
   logic                                                   prot_next;
   logic                                                   multi_next;
   logic                                                   cache_coherent_next;

   // Generate the VA Block rams and their surrounding logic
   generate
      for (z = 0; z < N_PAR_VA_RAMS; z++) begin : VA_RAMS
         check_ram
           #(
             .ADDR_WIDTH     ( AXI_S_ADDR_WIDTH  ),
             .RAM_DATA_WIDTH ( VA_RAM_DATA_WIDTH ),
             .PAGE_SIZE      ( PAGE_SIZE         ),
             .SET_WIDTH      ( SET_WIDTH         ),
             .OFFSET_WIDTH   ( OFFSET_WIDTH      )
             )
         u_check_ram
             (
              .clk_i         ( clk_i                      ),
              .rst_ni        ( rst_ni                     ),
              .in_addr_min   ( in_addr_min_i              ),
              .in_addr_max   ( in_addr_max_i              ),
              .rw_type       ( rw_type_i                  ),
              .partial_match ( invalidate_i               ),
              .ram_we        ( ram_we[z]                  ),
              .port0_addr    ( port0_addr[z]              ),
              .port1_addr    ( port1_addr                 ),
              .ram_wdata     ( ram_wdata                  ),
              .output_sent   ( output_sent | invalidate_i ), // always drop earlier detected hits immediately when invalidating
              .output_valid  ( va_output_valid            ),
              .offset_addr_d ( offset_addr_d              ),
              .hit_addr      ( hit_addr[z]                ),
              .master        ( cache_coherent[z]          ),
              .hit           ( hit[z]                     ),
              .multi_hit     ( multi_hit[z]               ),
              .prot          ( prot[z]                    )
              );
      end // for (z = 0; z < N_PORTS; z++)
   endgenerate

   ////////////////// ---------------- Control and Address --------------- ////////////////////////
   // FSM
   always_ff @(posedge clk_i) begin
      if (rst_ni == 0) begin
         search_SP <= IDLE;
      end else begin
         search_SP <= search_SN;
      end
   end

   always_comb begin : SEARCH_FSM
      search_SN         = search_SP;
      busy_o            = 1'b0;
      searching         = 1'b0;
      search_done       = 1'b0;
      last_search_next  = 1'b0;
      first_search_next = first_search;
      first_set_next    = first_set;

      set_num_d         = set_num_q;
      rollback          = 1'b0;

      unique case (search_SP)
        IDLE : begin
          if (start_i) begin
            search_SN         = SEARCH;
            first_search_next = 1'b1;
            first_set_next    = 1'b1;
          end
        end

        SEARCH : begin
          busy_o = 1'b1;

          // detect first set searched
          if (first_set) begin
            set_num_d      = min_set_num;
            first_set_next = 1'b0;
          end

          // detect last search cycle
          if ((first_search == 1'b0) && (offset_addr == offset_end_addr))
            last_search_next = 1'b1;

          // pause search during VA RAM reconfigration
          if (|ram_we) begin
            searching = 1'b0;
            if (invalidate_i && searching_q && !we_i) begin
              // we need to rollback to check other port that might also have been hit
              rollback         = 1'b1;
              last_search_next = 1'b0;
            end
          end else begin
            searching         = 1'b1;
            first_search_next = 1'b0;
          end

          if (va_output_valid) begin
            if ((last_search && !rollback) && set_num != max_set_num ) begin
              // search next set
              set_num_d         = set_num + 1;
              searching         = 1'b0;
              first_search_next = 1'b1;
`ifdef MULTI_HIT_FULL_SET
            end else if ((last_search & !rollback) | (!invalidate_i & (prot_top | multi_hit_top))) begin
`else
            end else if ((last_search & !rollback) | (!invalidate_i & (prot_top | multi_hit_top | hit_top))) begin
`endif
              // finish search
              search_SN      = DONE;
              search_done    = 1'b1;
            end
          end
        end

        DONE : begin
          busy_o = 1'b1;
          if (out_valid_o & out_ready_i)
            search_SN = IDLE;
        end

        default : begin
          search_SN = IDLE;
        end
      endcase // case (prot_SP)
   end // always_comb begin

   always_ff @(posedge clk_i) begin
      if (rst_ni == 0) begin
         last_search  <= 1'b0;
         first_search <= 1'b0;
         first_set    <= 1'b0;
      end else begin
         last_search  <= last_search_next;
         first_search <= first_search_next;
         first_set    <= first_set_next;
      end
  end

   /*
    * VA RAM address generation
    *
    * The input address and set number, and thus the offset start address, are available in the
    * cycle after the start signal. The buffered offset_addr becomes available one cycle later.
    * During the first search cycle, we therefore directly use offset_addr_start for the lookup.
    */
   assign min_set_num = in_addr_min_i[SET_WIDTH+IGNORE_LSB-1 : IGNORE_LSB];
   assign max_set_num = (in_addr_min_i[AXI_S_ADDR_WIDTH-1:SET_WIDTH+IGNORE_LSB] == in_addr_max_i[AXI_S_ADDR_WIDTH-1:SET_WIDTH+IGNORE_LSB]) ?
                        in_addr_max_i[SET_WIDTH+IGNORE_LSB-1 : IGNORE_LSB] :
                        min_set_num - 1'b1;
   assign set_num = first_set ? min_set_num : set_num_q;

   assign port0_raddr[OFFSET_WIDTH] = 1'b0;
   assign port1_addr [OFFSET_WIDTH] = 1'b1;

   assign port0_raddr[OFFSET_WIDTH-1:0] = first_search ? offset_start_addr : offset_addr;
   assign port1_addr [OFFSET_WIDTH-1:0] = first_search ? offset_start_addr : offset_addr;

   assign port0_raddr[SET_WIDTH+OFFSET_WIDTH : OFFSET_WIDTH+1] = set_num;
   assign port1_addr [SET_WIDTH+OFFSET_WIDTH : OFFSET_WIDTH+1] = set_num;

   always_comb begin
     for(int i=0; i<N_PAR_VA_RAMS; ++i) begin
       port0_addr[i] = ram_we[i] ? ram_waddr[i] : port0_raddr;
     end
   end

   // Store the set num to loop over it while invalidating
   always_ff @(posedge clk_i) begin
      if (rst_ni == 0) begin
         set_num_q <= 1'b0;
      end else begin
         set_num_q <= set_num_d;
      end
   end

   // The outputs of the BRAMs are only valid if in the previous cycle:
   // 1. the inputs were valid, and
   // 2. the BRAMs were not written to.
   // Otherwise, the outputs must be ignored.
   always_ff @(posedge clk_i) begin
      if (rst_ni == 0) begin
         searching_q <= 1'b0;
      end else begin
         searching_q <= searching;
      end
   end
   assign va_output_valid = searching_q;

   // Address offset for looking up the VA RAMs
   always_ff @(posedge clk_i) begin
      if (rst_ni == 0) begin
         offset_addr   <= 0;
      end else if (first_search) begin
         offset_addr <= offset_start_addr + 1'b1;
      end else if (searching) begin
         offset_addr <= offset_addr + 1'b1;
      end else if (rollback) begin
         offset_addr <= offset_addr - 1'b1;
      end
   end

   // Delayed address offest for looking up the PA RAM upon a hit in the VA RAMs
   always_ff @(posedge clk_i) begin
      if (rst_ni == 0) begin
         offset_addr_d <= 0;
      end else if (first_search) begin
         offset_addr_d <= offset_start_addr;
      end else if (searching) begin
         offset_addr_d <= offset_addr_d + 1'b1;
      end else if (rollback) begin
         offset_addr_d <= offset_addr_d - 1'b1;
      end
   end

   // Store the offset addr for hit to reduce latency for next search.
   generate
      if (HIT_OFFSET_STORE_WIDTH > 0) begin : OFFSET_STORE
`ifndef MULTI_HIT_FULL_SET
         logic [N_SETS-1:0][HIT_OFFSET_STORE_WIDTH-1:0] hit_offset_addr; // Contains offset addr for previous hit for every SET.
         logic [SET_WIDTH-1:0]                          set_num_reg;
         logic [SET_WIDTH+OFFSET_WIDTH+1-1:0]           hit_addr_reg;

         assign offset_start_addr = { hit_offset_addr[set_num] , {{OFFSET_WIDTH-HIT_OFFSET_STORE_WIDTH}{1'b0}} };
         assign offset_end_addr   =   hit_offset_addr[set_num]-1'b1;

         // Register the hit addr
         always_ff @(posedge clk_i) begin
            if (rst_ni == 0) begin
               hit_addr_reg <= 0;
               set_num_reg  <= 0;
            end else if (hit_top) begin
               hit_addr_reg <= hit_addr[hit_block_num];
               set_num_reg  <= set_num;
            end
         end

         // Store hit addr for each set. The next search in the same set will start from the saved addr.
         always_ff @(posedge clk_i) begin
            if (rst_ni == 0) begin
               hit_offset_addr <= 0;
            end else if (hit_o) begin
               hit_offset_addr[set_num_reg][HIT_OFFSET_STORE_WIDTH-1:0] <= hit_addr_reg[OFFSET_WIDTH-1 : (OFFSET_WIDTH - HIT_OFFSET_STORE_WIDTH)];
            end
         end
`else // No need to store offset if full multi hit detection is enabled because the entire SET is searched.
         assign offset_start_addr = 0;
         assign offset_end_addr   = {OFFSET_WIDTH{1'b1}};
`endif
      end else begin // if (HIT_OFFSET_STORE_WIDTH > 0)
         assign offset_start_addr = 0;
         assign offset_end_addr   = {OFFSET_WIDTH{1'b1}};
      end
   endgenerate

   assign prot_top = |prot;

   //////////////////////////////////////////////////////////////////////////////////////
   // check for hit, multi hit
   // In case of a multi hit, the hit_block_num indicates the lowest VA RAM with a hit.
   // In case of a multi hit in the same VA RAM, Port 0 is given priority.
   always_comb begin : HIT_CHECK
      hit_top       = |hit;
      hit_block_num = 0;
      first_hit_top = 1'b0;
      multi_hit_top = 1'b0;
      for (int i=N_PAR_VA_RAMS-1; i>=0; i--) begin
        if (hit[i] == 1'b1) begin
`ifdef MULTI_HIT_CUR_CYCLE
          if (multi_hit[i] | first_hit_top ) begin
            multi_hit_top = 1'b1;
          end
`endif
          first_hit_top = 1'b1;
          hit_block_num = i;
        end
      end // for (int i=0; i<N_PAR_VA_RAMS; i++)
   end // always_comb begin

   ///////////////////// ------------- Outputs ------------ //////////////////////////////////
   //// FSM
   always_ff @(posedge clk_i) begin
      if (rst_ni == 0) begin
         out_SP                     <= OUT_IDLE;
         pa_ram_store_data_SP       <= 1'b0;
         pa_port0_raddr_reg_SP      <=  'b0;
      end else begin
         out_SP                     <= out_SN;
         pa_ram_store_data_SP       <= pa_ram_store_data_SN;
         pa_port0_raddr_reg_SP      <= pa_port0_raddr_reg_SN;
      end
   end

   always_comb begin : OUTPUT_FSM
      out_SN                   = out_SP;

      miss_next                = miss_o;
      prot_next                = prot_o;
      multi_next               = multi_o;
      hit_next                 = hit_o;
      cache_coherent_next      = cache_coherent_o;
      pa_port0_raddr_reg_SN    = pa_port0_raddr_reg_SP;

      pa_port0_raddr           =  'b0;
      pa_ram_store_data_SN     = 1'b0;

      out_valid_o              = 1'b0;
      output_sent              = 1'b0;

      unique case (out_SP)
        OUT_IDLE : begin
           hit_next            = 1'b0;
           miss_next           = 1'b0;
           prot_next           = 1'b0;
           multi_next          = 1'b0;
           cache_coherent_next = 1'b0;

          // wait for search completed in input FSM
          if (search_done) begin
            // abort transaction
            if (~hit_top | prot_top | multi_hit_top) begin
              out_SN = SEND_OUTPUT;

              if (~hit_top) begin
                miss_next  = 1'b1;
              end
              if (prot_top) begin
                prot_next  = 1'b1;
                hit_next   = 1'b1;
              end
              if (multi_hit_top) begin
                multi_next = 1'b1;
                hit_next   = 1'b1;
              end
            // read PA RAM
            end else begin
              hit_next              = 1'b1;
              cache_coherent_next   = cache_coherent[hit_block_num];
              pa_port0_raddr        = (N_PAR_VA_RAMS * hit_addr[hit_block_num]) + hit_block_num;
              pa_port0_raddr_reg_SN = pa_port0_raddr;

              // read PA RAM now
              if (~pa_ram_we) begin
                out_SN               = SEND_OUTPUT;
                pa_ram_store_data_SN = 1'b1;
              // read PA RAM after PA RAM reconfiguration
              end else begin // pa_ram_we
                out_SN               = WAIT_ON_WRITE;

              end
            end
          end
        end

        WAIT_ON_WRITE : begin
          if ( ~pa_ram_we ) begin
             out_SN               = SEND_OUTPUT;
             pa_port0_raddr       = pa_port0_raddr_reg_SP;
             pa_ram_store_data_SN = 1'b1;
          end
        end

        SEND_OUTPUT : begin
           out_valid_o  = 1'b1;
           if (out_ready_i) begin
              out_SN      = OUT_IDLE;
              output_sent = 1'b1;
           end
        end

        default : begin
           out_SN = OUT_IDLE;
        end

      endcase // case (out_SP)
   end // always_comb begin

   //// Output signals
   always_ff @(posedge clk_i) begin
      if (rst_ni == 0) begin
         miss_o           <= 1'b0;
         prot_o           <= 1'b0;
         multi_o          <= 1'b0;
         hit_o            <= 1'b0;
         cache_coherent_o <= 1'b0;
      end else begin
         miss_o           <= miss_next;
         prot_o           <= prot_next;
         multi_o          <= multi_next;
         hit_o            <= hit_next;
         cache_coherent_o <= cache_coherent_next;
      end
   end

   ///////////////////////////////////////////////////////////////////////////////////////////////////


  ///////////////////// --------------- Physical Address -------------- ////////////////////////////

  /// PA Block RAM
  ram_tp_no_change #(
        .ADDR_WIDTH( PA_RAM_ADDR_WIDTH ),
        .DATA_WIDTH( PA_RAM_DATA_WIDTH )
        )
  pa_ram
    (
      .clk   ( clk_i                          ),
      .we    ( pa_ram_we                      ),
      .addr0 ( pa_port0_addr                  ),
      .addr1 ( '0                             ),
      .d_i   ( wdata_i[PA_RAM_DATA_WIDTH-1:0] ),
      .d0_o  ( pa_port0_data                  ),
      .d1_o  (                                )
    );

   assign out_addr_o[IGNORE_LSB-1:0]                = in_addr_min_i[IGNORE_LSB-1:0];
   assign out_addr_o[AXI_M_ADDR_WIDTH-1:IGNORE_LSB] = pa_data;

   always_ff @(posedge clk_i) begin
      if (rst_ni == 0) begin
         pa_port0_data_reg <= 0;
      end else if (pa_ram_store_data_SP) begin
         pa_port0_data_reg <= pa_port0_data;
      end
   end

   assign pa_data = pa_ram_store_data_SP ? pa_port0_data : pa_port0_data_reg;

   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

   // Write enable for all block rams
   generate if (LL_WIDTH != 0) begin
     always_comb begin
       var reg[LL_WIDTH:0] para;
       var int             para_int;
       for (para = 0; para < N_PAR_VA_RAMS; para=para+1'b1) begin
         para_int         = int'(para);
         if (we_i) begin
           ram_we[para_int]    = (waddr_i[LL_WIDTH+VA_RAM_ADDR_WIDTH] == 1'b0) && (waddr_i[LL_WIDTH-1:0] == para);
           ram_waddr[para_int] = waddr_i[LL_WIDTH+VA_RAM_ADDR_WIDTH-1:LL_WIDTH];
         end else if(invalidate_i) begin
           ram_we[para_int]    = hit[para_int];
           ram_waddr[para_int] = hit_addr[para_int];
         end else begin
           ram_we[para_int]    = 'b0;
           ram_waddr[para_int] = 'b0;
         end
       end
     end
   end else begin
     always_comb begin
       if (we_i) begin
         ram_we[0]    = (waddr_i[LL_WIDTH+VA_RAM_ADDR_WIDTH] == 1'b0);
         ram_waddr[0] = waddr_i[LL_WIDTH+VA_RAM_ADDR_WIDTH-1:LL_WIDTH];
       end else if(invalidate_i) begin
         ram_we[0]    = hit[0];
         ram_waddr[0] = hit_addr[0];
       end else begin
         ram_we[0]    = 'b0;
         ram_waddr[0] = 'b0;
       end
     end
   end
   endgenerate

   // Write data for all block rams
   always_comb begin
     if (we_i) begin
       ram_wdata = wdata_i[VA_RAM_DATA_WIDTH-1:0];
     end else begin
       ram_wdata = 'b0;
     end
   end

   // Addresses are word, not byte addresses
   // waddr_i[LL_WIDTH+VA_RAM_ADDR_WIDTH] will be 0 for all VA writes and 1 for all PA writes
   assign pa_ram_we      = we_i && (waddr_i[LL_WIDTH+VA_RAM_ADDR_WIDTH] == 1'b1);
   assign pa_port0_waddr = waddr_i[PA_RAM_ADDR_WIDTH-1:0];
   assign pa_port0_addr  = pa_ram_we ? pa_port0_waddr : pa_port0_raddr;

endmodule

// vim: ts=3 sw=3 sts=3 et nosmartindent autoindent foldmethod=marker tw=100
