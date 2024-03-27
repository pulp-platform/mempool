// Copyright 2020 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

/// Snitch Configuration.
package snitch_pkg;

  import cf_math_pkg::idx_width;

  localparam DataWidth                  = 32;
  localparam StrbWidth                  = DataWidth/8;
  localparam int NumFPOutstandingLoads  = 4;
  // Use a high number of outstanding loads, if running a latency-throughput analysis
  localparam int NumIntOutstandingLoads = `ifdef TRAFFIC_GEN 2048 `else 8 `endif;
  localparam MetaIdWidth                = idx_width(NumIntOutstandingLoads);
  // Xpulpimg extension enabled?
  localparam bit XPULPIMG = `ifdef XPULPIMG `XPULPIMG `else 1'bX `endif;
  // ZFINX extension enabled?
  localparam bit ZFINX = `ifdef ZFINX `ZFINX `else 1'bX `endif;
  // ZQUARTERINX extension enabled?
  localparam bit ZQUARTERINX = `ifdef ZQUARTERINX `ZQUARTERINX `else 1'bX `endif;
  // XDivSqrt extension enabled?
  localparam bit XDIVSQRT = `ifdef XDIVSQRT `XDIVSQRT `else 1'bX `endif;

  typedef logic [31:0]               addr_t;
  typedef logic [DataWidth-1:0]      data_t;
  typedef logic [StrbWidth-1:0]      strb_t;
  typedef logic [MetaIdWidth-1:0]    meta_id_t;

  typedef struct packed {
    addr_t       BootAddress;
    int unsigned NrCores;
  } SnitchCfg;

  typedef struct packed {
    addr_t addr;
    meta_id_t id;
    logic [3:0] amo;
    logic write;
    data_t data;
    strb_t strb;
  } dreq_t;

  typedef struct packed {
    data_t data;
    meta_id_t id;
    logic write;
    logic error;
  } dresp_t;

  typedef enum logic [2:0] {
    XPULP_IPU = 0,
    FP_SS = 1,
    FP_DIVSQRT = 2
  } acc_addr_e;

  typedef struct packed {
    acc_addr_e addr;
    logic [4:0] id;
    logic [31:0] data_op;
    data_t data_arga;
    data_t data_argb;
    data_t data_argc;
  } acc_req_t;

  typedef struct packed {
    acc_addr_e addr;
    logic [4:0] id;
    logic [5:0] hart_id;
    logic [31:0] data_op;
    data_t data_arga;
    data_t data_argb;
    data_t data_argc;
  } sh_acc_req_t;

  typedef struct packed {
    logic [4:0] id;
    logic error;
    data_t data;
  } acc_resp_t;

  typedef struct packed {
    logic [4:0] id;
    logic [5:0] hart_id;
    logic error;
    data_t data;
  } sh_acc_resp_t;

  // Number of instructions the sequencer can hold
  localparam int FPUSequencerInstr      = 16;
  // SSRs
  localparam logic [31:0] SSR_ADDR_BASE = 32'h20_4800;
  localparam logic [31:0] SSR_ADDR_MASK = 32'hffff_fe00;
  localparam logic [11:0] CSR_SSR       = 12'h7C0;
  localparam int SSRNrCredits           = 4;
  // Registers which are used as SSRs
  localparam [4:0] FT0                  = 5'b0;
  localparam [4:0] FT1                  = 5'b1;
  localparam [1:0][4:0] SSRRegs         = {FT1, FT0};
  function automatic logic is_ssr(logic [4:0] register);
    unique case (register)
      FT0, FT1: return 1'b1;
      default : return 0;
    endcase
  endfunction

  // FPU
  // Floating-point extensions configuration
  localparam bit RVF = 1; // Is F extension enabled - MUST BE 1 IF D ENABLED!
  localparam bit RVD = 0; // Is D extension enabled

  // Transprecision floating-point extensions configuration
  localparam bit XF16    = 1; // Is half-precision float extension (Xf16) enabled
  localparam bit XF16ALT = 0; // Is alt. half-precision float extension (Xf16alt) enabled
  localparam bit XF8     = ZQUARTERINX; // Is quarter-precision float extension (Xf8) enabled
  localparam bit XF8ALT  = 0; // Is alt. quarter-precision float extension (Xf8alt) enabled
  localparam bit XFVEC   = 1; // Is vectorial float SIMD extension (Xfvec) enabled
  localparam bit XDivSqrt = XDIVSQRT; // Enable div/sqrt unit (buggy - use with caution)
  // Non-standard extension present
  localparam bit NSX = XF16 | XF16ALT | XF8 | XFVEC;
  // ------------------
  // FPU Configuration
  // ------------------
  localparam bit FP_PRESENT = RVF | RVD | XF16 | XF16ALT | XF8;

  localparam FLEN = RVD     ? 64 : // D ext.
                    RVF     ? 32 : // F ext.
                    XF16    ? 16 : // Xf16 ext.
                    XF16ALT ? 16 : // Xf16alt ext.
                    XF8     ? 8 :  // Xf8 ext.
                    0;             // Unused in case of no FP

  localparam fpnew_pkg::fpu_features_t FPU_FEATURES = '{
    Width:         fpnew_pkg::maximum(FLEN, 32),
    EnableVectors: XFVEC,
    EnableNanBox:  1'b0,
    FpFmtMask:     {RVF, RVD, XF16, XF8, XF16ALT, XF8ALT},
    IntFmtMask:    {XFVEC && XF8, XFVEC && (XF16 || XF16ALT), 1'b1, 1'b0}
  };

  // Latencies of FP ops (number of regs)
  localparam int unsigned LAT_COMP_FP32    = 'd1;
  localparam int unsigned LAT_COMP_FP64    = 'd0;
  localparam int unsigned LAT_COMP_FP16    = 'd0;
  localparam int unsigned LAT_COMP_FP16ALT = 'd0;
  localparam int unsigned LAT_COMP_FP8     = 'd0;
  localparam int unsigned LAT_COMP_FP8ALT  = 'd0;
  localparam int unsigned LAT_DIVSQRT      = 'd2;
  localparam int unsigned LAT_NONCOMP      = 'd1;
  localparam int unsigned LAT_CONV         = 'd2;
  localparam int unsigned LAT_SDOTP        = 'd2;

  localparam fpnew_pkg::fpu_implementation_t FPU_IMPLEMENTATION = '{
    PipeRegs:  '{// FP32, FP64, FP16, FP8, FP16alt
                 '{ LAT_COMP_FP32,
                    LAT_COMP_FP64,
                    LAT_COMP_FP16,
                    LAT_COMP_FP8,
                    LAT_COMP_FP16ALT,
                    LAT_COMP_FP8ALT}, // ADDMUL
                 '{default: LAT_DIVSQRT}, // DIVSQRT
                 '{default: LAT_NONCOMP}, // NONCOMP
                 '{default: LAT_CONV},    // CONV
                 '{default: LAT_SDOTP}},  // SDOTP
    UnitTypes: '{'{default: fpnew_pkg::MERGED}, // ADDMUL
                 '{default: fpnew_pkg::DISABLED}, // DIVSQRT
                 '{default: fpnew_pkg::PARALLEL}, // NONCOMP
                 '{default: fpnew_pkg::MERGED},   // CONV
                 '{default: fpnew_pkg::MERGED}},  // SDOTP
    PipeConfig: fpnew_pkg::BEFORE
  };

  // Tile-shared divsqrt unit implemented as fpnew
  localparam fpnew_pkg::fpu_implementation_t DIVSQRT_IMPLEMENTATION = '{
    PipeRegs:  '{// FP32, FP64, FP16, FP8, FP16alt
                 '{ LAT_COMP_FP32,
                    LAT_COMP_FP64,
                    LAT_COMP_FP16,
                    LAT_COMP_FP8,
                    LAT_COMP_FP16ALT,
                    LAT_COMP_FP8ALT}, // ADDMUL
                 '{default: LAT_DIVSQRT}, // DIVSQRT
                 '{default: LAT_NONCOMP}, // NONCOMP
                 '{default: LAT_CONV},    // CONV
                 '{default: LAT_SDOTP}},  // SDOTP
    UnitTypes: '{'{default: fpnew_pkg::DISABLED},   // ADDMUL
                 '{default:
                 `ifdef XDIVSQRT (fpnew_pkg::MERGED)
                 `else (fpnew_pkg::DISABLED) `endif}, // DIVSQRT
                 '{default: fpnew_pkg::DISABLED},   // NONCOMP
                 '{default: fpnew_pkg::DISABLED},   // CONV
                 '{default: fpnew_pkg::DISABLED}},  // SDOTP
    PipeConfig: fpnew_pkg::BEFORE
  };

  // Enable stocastic rounding
  localparam fpnew_pkg::rsr_impl_t FPU_RSR = '{
    EnableRSR:            1'b0,
    RsrPrecision:           12,
    LfsrInternalPrecision:  32
  };

  // Amount of address bit which should be used for accesses from the SoC side.
  // This effectively determines the Address Space of a Snitch Cluster.
  localparam logic [31:0] SoCRequestAddrBits = 32;

  // Address Map
  // TCDM, everything below 0x4000_0000
  localparam logic [31:0] TCDMStartAddress = 32'h0000_0000;
  localparam logic [31:0] TCDMMask         = '1 << 28;

  // Slaves on Cluster AXI Bus
  typedef enum integer {
    TCDM               = 0,
    ClusterPeripherals = 1,
    SoC                = 2
  } cluster_slave_e;

  typedef enum integer {
    CoreReq = 0,
    ICache  = 1,
    AXISoC  = 2
  } cluster_master_e;

  localparam int unsigned NrSlaves  = 3;
  localparam int unsigned NrMasters = 3;

  localparam int IdWidth      = 2;
  localparam int IdWidthSlave = $clog2(NrMasters) + IdWidth;

  //                                                    3. SoC         2. Cluster Peripherals  3. TCDM
  localparam logic [NrSlaves-1:0][31:0] StartAddress = {32'h8000_0000, 32'h4000_0000, TCDMStartAddress};
  localparam logic [NrSlaves-1:0][31:0] EndAddress   = {32'hFFFF_FFFF, 32'h5000_0000, TCDMStartAddress + 32'h1000_0000};
  localparam logic [NrSlaves-1:0] ValidRule          = {{NrSlaves}{1'b1}};

  // Cluster Peripheral Registers
  typedef enum logic [31:0] {
    TCDMStartAddressReg = 32'h4000_0000,
    TCDMEndAddressReg   = 32'h4000_0008,
    NrCoresReg          = 32'h4000_0010,
    FetchEnableReg      = 32'h4000_0018,
    ScratchReg          = 32'h4000_0020,
    WakeUpReg           = 32'h4000_0028,
    CycleCountReg       = 32'h4000_0030,
    BarrierReg          = 32'h4000_0038,
    TcdmAccessedReg     = 32'h4000_FFF0,
    TcdmCongestedReg    = 32'h4000_FFF8,
    PerfCounterBase     = 32'h4001_0000
  } cluster_peripheral_addr_e;

  // Offload to shared accelerator
  function automatic logic shared_offload (logic [31:0] instr);
    logic offload;
    unique casez (instr)
      riscv_instr::MUL,
      riscv_instr::MULH,
      riscv_instr::MULHSU,
      riscv_instr::MULHU,
      riscv_instr::DIV,
      riscv_instr::DIVU,
      riscv_instr::REM,
      riscv_instr::REMU,
      riscv_instr::MULW,
      riscv_instr::DIVW,
      riscv_instr::DIVUW,
      riscv_instr::REMW,
      riscv_instr::REMUW: offload = 1;
      default: offload            = 0;
    endcase
    return offload;
  endfunction

  // Event strobes per core, counted by the performance counters in the cluster
  // peripherals.
  typedef struct packed {
    logic issue_fpu;         // core operations performed in the FPU
    logic issue_fpu_seq;     // includes load/store operations
    logic issue_core_to_fpu; // instructions issued from core to FPU
    logic retired_insts;     // number of instructions retired by the core
  } core_events_t;

  // Event strobes per core, counted by the performance counters in the cluster
  // peripherals.
  typedef struct packed {
    logic issue_fpu;         // core operations performed in the FPU
    logic issue_core_to_fpu; // instructions issued from core to FPU
    logic retired_insts;     // number of instructions retired by the core
  } fp_ss_core_events_t;

  // Trace-Port Definitions
  typedef struct packed {
    longint acc_q_hs;
    longint fpu_out_hs;
    longint op_in;
    longint op_sel_0;
    longint op_sel_1;
    longint op_sel_2;
    longint src_fmt;
    longint dst_fmt;
    longint int_fmt;
    longint acc_qdata_0;
    longint acc_qdata_1;
    longint acc_qdata_2;
    longint op_0;
    longint op_1;
    longint op_2;
    longint use_fpu;
  } fpu_trace_port_t;

endpackage
