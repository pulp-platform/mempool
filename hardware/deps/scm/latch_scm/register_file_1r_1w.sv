// Copyright 2014-2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Company:        Institute of Integrated Systems // ETH Zurich              //
//                                                                            //
// Engineer:      Igor Loi - igor.loi@unibo.it                                //
//                                                                            //
// Additional contributions by:                                               //
//                 Francesco Conti                                            //
//                 Davide Rossi                                               //
//                 Michael Gautschi                                           //
//                 Antonio Pullini                                            //
//                                                                            //
// Create Date:    12/03/2015                                                 //
// Design Name:    scm memory                                                 //
// Module Name:    register_file_1r_1w                                        //
// Project Name:   HWCE                                                       //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    scm memory multiport: FOR HWCE                             //
//                                                                            //
// Revision:                                                                  //
// Revision v0.1 - File Created                                               //
// Revision v0.2 - Improved Identation                                        //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module register_file_1r_1w
#(
    parameter ADDR_WIDTH    = 5,
    parameter DATA_WIDTH    = 32
)
(
    input  logic                                  clk,

    // Read port
    input  logic                                  ReadEnable,
    input  logic [ADDR_WIDTH-1:0]                 ReadAddr,
    output logic [DATA_WIDTH-1:0]                 ReadData,


    // Write port
    input  logic                                  WriteEnable,
    input  logic [ADDR_WIDTH-1:0]                 WriteAddr,
    input  logic [DATA_WIDTH-1:0]                 WriteData
);

    localparam    NUM_WORDS = 2**ADDR_WIDTH;

    // Read address register, located at the input of the address decoder
    logic [ADDR_WIDTH-1:0]                        RAddrRegxDP;
    logic [NUM_WORDS-1:0]                         RAddrOneHotxD;


    logic [DATA_WIDTH-1:0]                        MemContentxDP[NUM_WORDS];

    logic [NUM_WORDS-1:0]                         WAddrOneHotxD;
    logic [NUM_WORDS-1:0]                         ClocksxC;
    logic [DATA_WIDTH-1:0]                        WDataIntxD;

    logic                                         clk_int;

    int unsigned i;
    int unsigned j;
    int unsigned k;
    int unsigned l;
    int unsigned m;

    genvar x;
    genvar y;

    cluster_clock_gating CG_WE_GLOBAL
    (
        .clk_o     ( clk_int       ),
        .en_i      ( WriteEnable   ),
        .test_en_i ( 1'b0          ),
        .clk_i     ( clk           )
    );

    //-----------------------------------------------------------------------------
    //-- READ : Read address register
    //-----------------------------------------------------------------------------
    always_ff @(posedge clk)
    begin : p_RAddrReg
        if(ReadEnable)
            RAddrRegxDP <= ReadAddr;
    end


    //-----------------------------------------------------------------------------
    //-- READ : Read address decoder RAD
    //-----------------------------------------------------------------------------
    always_comb
    begin : p_RAD
        RAddrOneHotxD = '0;
        RAddrOneHotxD[RAddrRegxDP] = 1'b1;
    end
    assign ReadData = MemContentxDP[RAddrRegxDP];


    //-----------------------------------------------------------------------------
    //-- WRITE : Write Address Decoder (WAD), combinatorial process
    //-----------------------------------------------------------------------------
    always_comb
    begin : p_WAD
        for(i=0; i<NUM_WORDS; i++)
        begin : p_WordIter
            if ( (WriteEnable == 1'b1 ) && (WriteAddr == i) )
                WAddrOneHotxD[i] = 1'b1;
            else
                WAddrOneHotxD[i] = 1'b0;
        end
    end

    //-----------------------------------------------------------------------------
    //-- WRITE : Clock gating (if integrated clock-gating cells are available)
    //-----------------------------------------------------------------------------
    generate
    for(x=0; x<NUM_WORDS; x++)
    begin : CG_CELL_WORD_ITER
        cluster_clock_gating CG_Inst
        (
            .clk_o     ( ClocksxC[x]      ),
            .en_i      ( WAddrOneHotxD[x] ),
            .test_en_i ( 1'b0             ),
            .clk_i     ( clk_int          )
        );
    end
    endgenerate

    //-----------------------------------------------------------------------------
    // WRITE : SAMPLE INPUT DATA
    //-----------------------------------------------------------------------------
    always_ff @(posedge clk)
    begin : sample_waddr
        if(WriteEnable)
            WDataIntxD <= WriteData;
    end


    //-----------------------------------------------------------------------------
    //-- WRITE : Write operation
    //-----------------------------------------------------------------------------
    //-- Generate M = WORDS sequential processes, each of which describes one
    //-- word of the memory. The processes are synchronized with the clocks
    //-- ClocksxC(i), i = 0, 1, ..., M-1
    //-- Use active low, i.e. transparent on low latches as storage elements
    //-- Data is sampled on rising clock edge

    always_latch
    begin : latch_wdata
        for(k=0; k<NUM_WORDS; k++)
        begin : w_WordIter
            if( ClocksxC[k] == 1'b1)
              MemContentxDP[k] = WDataIntxD;
        end
    end

endmodule
