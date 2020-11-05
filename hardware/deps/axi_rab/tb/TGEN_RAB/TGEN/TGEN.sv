// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

`timescale 1ns/1ps
`define SOD 0.1

module TGEN
#(
  parameter AXI4_ADDRESS_WIDTH = 32,
  parameter AXI4_RDATA_WIDTH   = 64,
  parameter AXI4_WDATA_WIDTH   = 64,
  parameter AXI4_ID_WIDTH      = 6,
  parameter AXI4_USER_WIDTH    = 10,
  parameter AXI_NUMBYTES       = AXI4_WDATA_WIDTH/8,
  parameter SRC_ID             = 0
)
(
  input logic                                           ACLK,
  input logic                                           ARESETn,

  // ---------------------------------------------------------------
  // AXI TARG Port Declarations ------------------------------------
  // ---------------------------------------------------------------
  //AXI write address bus -------------- // USED// --------------
  output  logic [AXI4_ID_WIDTH-1:0]                    AWID     ,
  output  logic [AXI4_ADDRESS_WIDTH-1:0]               AWADDR   ,
  output  logic [ 7:0]                                 AWLEN    ,
  output  logic [ 2:0]                                 AWSIZE   ,
  output  logic [ 1:0]                                 AWBURST  ,
  output  logic                                        AWLOCK   ,
  output  logic [ 3:0]                                 AWCACHE  ,
  output  logic [ 2:0]                                 AWPROT   ,
  output  logic [ 3:0]                                 AWREGION ,
  output  logic [ AXI4_USER_WIDTH-1:0]                 AWUSER   ,
  output  logic [ 3:0]                                 AWQOS    ,
  output  logic                                        AWVALID  ,
  input   logic                                        AWREADY  ,
  // ---------------------------------------------------------------

  //AXI write data bus -------------- // USED// --------------
  output  logic [AXI4_WDATA_WIDTH-1:0]                 WDATA  ,
  output  logic [AXI_NUMBYTES-1:0]                     WSTRB  ,
  output  logic                                        WLAST  ,
  output  logic [AXI4_USER_WIDTH-1:0]                  WUSER  ,
  output  logic                                        WVALID ,
  input   logic                                        WREADY ,
  // ---------------------------------------------------------------

  //AXI write response bus -------------- // USED// --------------
  input   logic   [AXI4_ID_WIDTH-1:0]                  BID    ,
  input   logic   [ 1:0]                               BRESP  ,
  input   logic                                        BVALID ,
  input   logic   [AXI4_USER_WIDTH-1:0]                BUSER  ,
  output  logic                                        BREADY ,
  // ---------------------------------------------------------------

  //AXI read address bus -------------------------------------------
  output  logic [AXI4_ID_WIDTH-1:0]                    ARID,
  output  logic [AXI4_ADDRESS_WIDTH-1:0]               ARADDR,
  output  logic [ 7:0]                                 ARLEN,
  output  logic [ 2:0]                                 ARSIZE,
  output  logic [ 1:0]                                 ARBURST,
  output  logic                                        ARLOCK,
  output  logic [ 3:0]                                 ARCACHE,
  output  logic [ 2:0]                                 ARPROT,
  output  logic [ 3:0]                                 ARREGION,
  output  logic [ AXI4_USER_WIDTH-1:0]                 ARUSER,
  output  logic [ 3:0]                                 ARQOS,
  output  logic                                        ARVALID,
  input   logic                                        ARREADY,
  // ---------------------------------------------------------------

  //AXI read data bus ----------------------------------------------
  input  logic [AXI4_ID_WIDTH-1:0]                     RID,
  input  logic [AXI4_RDATA_WIDTH-1:0]                  RDATA,
  input  logic [ 1:0]                                  RRESP,
  input  logic                                         RLAST,
  input  logic [AXI4_USER_WIDTH-1:0]                   RUSER,
  input  logic                                         RVALID,
  output logic                                         RREADY,
  // ---------------------------------------------------------------

  output logic                                         eoc,
  input  logic                                         fetch_en,
  output logic [31:0]                                  PASS,
  output logic [31:0]                                  FAIL
);

  localparam COUNT_32B = 128;
  localparam COUNT_16B = 256;
  localparam COUNT_8B  = 512;
  localparam COUNT_4B  = 1024;
  localparam COUNT_ONE  = 1;

  //class color ;

  event                                       req_AW_granted;
  event                                       req_AR_granted;
  event                                       req_DW_granted;
  event                                       WriteDone;
  event                                       IncomingRead, IncomingLastRead;

  event                                       fetch_en_event;

  event                                       AW_barrier_exit;
  event                                       AR_barrier_exit;

  integer                                     i,j,k;
  integer                                     i_AR_queue, i_AW_queue;
  integer                                     AR_queue_found, AW_queue_found;
  integer                                     ID;

  int unsigned                                pending_AW;
  int unsigned                                pending_AR;

  integer                                     count_AW, count_W, count_AR;
  logic [4095:0]                              temp_wdata;

  logic                                       R_head_packet;
  int unsigned                                count_R_burst;

  logic [31:0]                                BASE_ADDRESS;

  int unsigned                                protocol_PASS = 0;
  int unsigned                                protocol_FAIL = 0;


  real                                        average_R_latency = 0;
  real                                        average_W_latency = 0;

  //Queue for write/Read to check data integrity
  struct
  {
    logic [AXI4_WDATA_WIDTH-1:0]              data;
    logic [AXI4_ADDRESS_WIDTH-1:0]            addr;
    logic [AXI4_ID_WIDTH-1:0]                 id;
    logic [AXI4_USER_WIDTH-1:0]               user;
    time                                      init_time;
  } B_temp_slot, R_temp_slot, AW_temp_slot, AR_temp_slot, AR_queue[$], AW_queue[$];


  time                                        AW_latency[$];
  time                                        AR_latency[$];

  logic                                       busy_AW, busy_AR, full_AW, full_AR;

    // Check if all request have receivced a valid response
    always @(posedge ACLK) begin

      if( (AWVALID == 1'b1) && (AWREADY == 1'b1) ) begin
        AW_temp_slot.addr      = AWADDR;
        AW_temp_slot.id        = AWID;
        AW_temp_slot.user      = AWUSER;
        AW_temp_slot.init_time = $time;
        AW_queue.push_front(AW_temp_slot);
      end

      if( (BVALID == 1'b1) && (BREADY == 1'b1) ) begin

        // Find the proper transaction in the list of outstanding ones, we can have reordering.
        AW_queue_found = 0;
        for (i_AW_queue=0; i_AW_queue<AW_queue.size(); i_AW_queue++) begin
          if (AW_queue[i_AW_queue].id == BID) begin
            B_temp_slot = AW_queue[i_AW_queue];
            AW_queue.delete(i_AW_queue);
            AW_queue_found = 1;
            break;
          end
        end
        if (AW_queue_found == 0) begin
          $error("No write transaction outstanding with ID = %x ", BID);
        end

        AW_latency.push_front($time-B_temp_slot.init_time);

        if ( (B_temp_slot.id == BID) &&
             ( ((BRESP == 2'b00) && (B_temp_slot.user == BUSER)) ||
               ((BRESP == 2'b10) && (             'b0 == BUSER)) ) ) begin
          // In the case of a RAB miss, BUSER does not contain the ID but is 0.
          protocol_PASS++;

        end else begin

          protocol_FAIL++;
          if (B_temp_slot.id != BID) begin
            $warning("KO in B channel: Expected BID   is %x while got %x ", B_temp_slot.id, BID);
          end
          if (B_temp_slot.user != BUSER) begin
            $warning("KO in B channel: Expected BUSER is %x while got %x ", B_temp_slot.user, BUSER);
          end
          if ( (BRESP != 2'b00) && (BRESP != 2'b10) ) begin
            $warning("KO in B channel: BRESP is %x", BRESP);
          end
        end

        //$display("OK for ID %d and latency = %t ns", BID,($time-B_temp_slot.init_time)/1000.0);

      end

      case(AW_queue.size())
        0:         begin busy_AW = 1'b0; full_AW = 1'b0; -> AW_barrier_exit; end
        15:        begin busy_AW = 1'b1; full_AW = 1'b1; end
        default :  begin busy_AW = 1'b1; full_AW = 1'b0; end
      endcase

      pending_AW = AW_queue.size();

      if( (ARVALID == 1'b1) && (ARREADY == 1'b1) ) begin
        AR_temp_slot.addr      = ARADDR;
        AR_temp_slot.id        = ARID;
        AR_temp_slot.user      = ARUSER;
        AR_temp_slot.init_time = $time;
        AR_queue.push_front(AR_temp_slot);
      end

      if( (RVALID == 1'b1) && (RREADY == 1'b1) ) begin

        if (R_head_packet) begin
          // Find the proper transaction in the list of outstanding ones, we can have reordering.
          AR_queue_found = 0;
          for (i_AR_queue=0; i_AR_queue<AR_queue.size(); i_AR_queue++) begin
            if (AR_queue[i_AR_queue].id == RID) begin
              R_temp_slot = AR_queue[i_AR_queue];
              AR_queue.delete(i_AR_queue);
              AR_queue_found = 1;
              break;
            end
          end
          if (AR_queue_found == 0) begin
            $error("No read transaction outstanding with ID = %x ", RID);
          end
          R_head_packet = 0;
        end

        AR_latency.push_front($time-R_temp_slot.init_time);

        if ( (R_temp_slot.id == RID) &&
             ( ((RRESP == 2'b00) && (R_temp_slot.user == RUSER)) ||
               ((RRESP == 2'b10) && (             'b0 == RUSER)) ) ) begin
          // In the case of a RAB miss, RUSER does not contain the ID but is 0.
          protocol_PASS++;

        end else begin

          protocol_FAIL++;
          if (R_temp_slot.id != RID) begin
            $warning("KO in R channel: Expected RID   is %x while got %x ", R_temp_slot.id, RID);
          end
          if (R_temp_slot.user != RUSER) begin
            $warning("KO in R channel: Expected RUSER is %x while got %x ", R_temp_slot.user, RUSER);
          end
          if ( (RRESP != 2'b00) && (RRESP != 2'b10) ) begin
            $warning("KO in R channel: RRESP is %x", RRESP);
          end
        end

        count_R_burst++;

        if( RLAST == 1'b1  ) begin
          R_head_packet = 1'b1;
          count_R_burst = '0;
          //$display("Latency for LOAD = %t ns",($time-R_temp_slot.init_time)/1000.0 );
        end
      end

      case(AR_queue.size())
          0:         begin busy_AR = 1'b0; full_AR = 1'b0; -> AR_barrier_exit; end
          15:        begin busy_AR = 1'b1; full_AR = 1'b1; end
          default :  begin busy_AR = 1'b1; full_AR = 1'b0; end
      endcase

      pending_AR = AR_queue.size();

      if ( (pending_AR > 0) && ( ($time - AR_temp_slot.init_time)/1000.0 > 1000) ) begin
        $error("TIME_OUT error on AR channel");
      end

      if ( (pending_AW > 0) && ( (($time - AW_temp_slot.init_time)/1000.0) > 1000) ) begin
        $error("TIME_OUT error on AW channel");
      end
    end

    assign BREADY = 1'b1;
    assign RREADY = 1'b1;

    `include "TGEN_TASK.sv"
    `include "TGEN_TASK_ADDON.sv"

    always @(posedge ACLK)
    begin
        if(fetch_en)
          -> fetch_en_event;
    end

    always @(posedge ACLK)
    begin
      if((AWVALID == 1'b1) && (AWREADY == 1'b1))
      begin
        -> req_AW_granted;
      end
    end

    always @(posedge ACLK)
    begin
      if((ARVALID == 1'b1) && (ARREADY == 1'b1))
      begin
        -> req_AR_granted;
      end
    end

    always @(posedge ACLK)
    begin
      if((WVALID == 1'b1) && (WREADY == 1'b1))
      begin
        -> req_DW_granted;
      end
    end

    always @(posedge ACLK)
    begin
      if((BVALID == 1'b1) && (BREADY == 1'b1))
      begin
        -> WriteDone;
      end
    end

    always @(posedge ACLK) begin
      if((RVALID == 1'b1) && (RREADY == 1'b1)) begin
        -> IncomingRead;
        if(RLAST)
          -> IncomingLastRead;
      end
    end

initial
  begin
    eoc = 1'b0;
    PASS = 0;
    FAIL = 0;
    R_head_packet = 1'b1;

    Nop_AR();
    Nop_AW();
    Nop_DW();

    @(posedge ACLK);
    @(posedge ACLK);
    @(posedge ACLK);
    @(posedge ACLK);
    @(posedge ACLK);
    @(posedge ACLK);
    @(posedge ACLK);
    @(posedge ACLK);
    @(posedge ACLK);
    @(posedge ACLK);
    @(posedge ACLK);
    @(posedge ACLK);


    repeat (1) begin
      @(fetch_en_event);

      case(SRC_ID)
        0:  begin `include  "TRAFFIC_0_00.cmd"; end
        1:  begin `include  "TRAFFIC_0_01.cmd"; end
        2:  begin `include  "TRAFFIC_0_02.cmd"; end
        3:  begin `include  "TRAFFIC_0_03.cmd"; end
        4:  begin `include  "TRAFFIC_0_04.cmd"; end
        5:  begin `include  "TRAFFIC_0_05.cmd"; end
        6:  begin `include  "TRAFFIC_0_06.cmd"; end
        7:  begin `include  "TRAFFIC_0_07.cmd"; end
        8:  begin `include  "TRAFFIC_0_08.cmd"; end
        9:  begin `include  "TRAFFIC_0_09.cmd"; end
        10: begin `include  "TRAFFIC_0_10.cmd"; end
        11: begin `include  "TRAFFIC_0_11.cmd"; end
        12: begin `include  "TRAFFIC_0_12.cmd"; end
        13: begin `include  "TRAFFIC_0_13.cmd"; end
        14: begin `include  "TRAFFIC_0_14.cmd"; end
        15: begin `include  "TRAFFIC_0_15.cmd"; end
        16: begin `include  "TRAFFIC_DMA_CFG.cmd"; end

      default: begin Nop(); end

      endcase
    end

    Nop_AR();
    Nop_AW();
    Nop_DW();
    @(negedge ACLK);
    @(negedge ACLK);
    @(negedge ACLK);
    @(negedge ACLK);
    @(negedge ACLK);
    @(negedge ACLK);
    @(negedge ACLK);
    @(negedge ACLK);
    @(negedge ACLK);

    for (k = 0; k <  AW_latency.size(); k++) begin
      average_W_latency = average_W_latency +  AW_latency[k];
    end
    if (AW_latency.size()) begin
      average_W_latency = average_W_latency/AW_latency.size();
    end

    for (k = 0; k <  AR_latency.size(); k++) begin
      average_R_latency = average_R_latency +  AR_latency[k];
    end
    if (AR_latency.size()) begin
      average_R_latency = average_R_latency/AR_latency.size();
    end

    $write   ("CORE[%1d]:\t  Average READ  latency for  is %.1f [cycles]; \t\t", SRC_ID, average_R_latency);
    $display ("Average WRITE latency is %.1f [cycles]: MIXED TRAFFIC", average_W_latency);
    eoc = 1'b1;
end

endmodule
