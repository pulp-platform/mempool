// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Register Package auto-generated by `reggen` containing data structure

package control_registers_reg_pkg;

  // Param list
  parameter int ROCacheNumAddrRules = 4;
  parameter int MAX_NumGroups = 64;

  // Address widths within the block
  parameter int BlockAw = 9;

  ////////////////////////////
  // Typedefs for registers //
  ////////////////////////////

  typedef struct packed {
    logic [31:0] q;
  } control_registers_reg2hw_eoc_reg_t;

  typedef struct packed {
    logic [31:0] q;
    logic        qe;
  } control_registers_reg2hw_wake_up_reg_t;

  typedef struct packed {
    logic [31:0] q;
    logic        qe;
  } control_registers_reg2hw_wake_up_tile_mreg_t;

  typedef struct packed {
    logic [31:0] q;
    logic        qe;
  } control_registers_reg2hw_wake_up_group_reg_t;

  typedef struct packed {
    logic [31:0] q;
    logic        qe;
  } control_registers_reg2hw_wake_up_cluster_reg_t;

  typedef struct packed {
    logic [31:0] q;
  } control_registers_reg2hw_ro_cache_enable_reg_t;

  typedef struct packed {
    logic [31:0] q;
  } control_registers_reg2hw_ro_cache_flush_reg_t;

  typedef struct packed {
    logic [31:0] q;
    logic        qe;
  } control_registers_reg2hw_ro_cache_start_mreg_t;

  typedef struct packed {
    logic [31:0] q;
    logic        qe;
  } control_registers_reg2hw_ro_cache_end_mreg_t;

  typedef struct packed {
    logic [31:0] d;
  } control_registers_hw2reg_tcdm_start_address_reg_t;

  typedef struct packed {
    logic [31:0] d;
  } control_registers_hw2reg_tcdm_end_address_reg_t;

  typedef struct packed {
    logic [31:0] d;
  } control_registers_hw2reg_nr_cores_reg_reg_t;

  typedef struct packed {
    logic [31:0] d;
  } control_registers_hw2reg_ro_cache_start_mreg_t;

  typedef struct packed {
    logic [31:0] d;
  } control_registers_hw2reg_ro_cache_end_mreg_t;

  // Register -> HW type
  typedef struct packed {
    control_registers_reg2hw_eoc_reg_t eoc; // [2570:2539]
    control_registers_reg2hw_wake_up_reg_t wake_up; // [2538:2506]
    control_registers_reg2hw_wake_up_tile_mreg_t [63:0] wake_up_tile; // [2505:394]
    control_registers_reg2hw_wake_up_group_reg_t wake_up_group; // [393:361]
    control_registers_reg2hw_wake_up_cluster_reg_t wake_up_cluster; // [360:328]
    control_registers_reg2hw_ro_cache_enable_reg_t ro_cache_enable; // [327:296]
    control_registers_reg2hw_ro_cache_flush_reg_t ro_cache_flush; // [295:264]
    control_registers_reg2hw_ro_cache_start_mreg_t [3:0] ro_cache_start; // [263:132]
    control_registers_reg2hw_ro_cache_end_mreg_t [3:0] ro_cache_end; // [131:0]
  } control_registers_reg2hw_t;

  // HW -> register type
  typedef struct packed {
    control_registers_hw2reg_tcdm_start_address_reg_t tcdm_start_address; // [351:320]
    control_registers_hw2reg_tcdm_end_address_reg_t tcdm_end_address; // [319:288]
    control_registers_hw2reg_nr_cores_reg_reg_t nr_cores_reg; // [287:256]
    control_registers_hw2reg_ro_cache_start_mreg_t [3:0] ro_cache_start; // [255:128]
    control_registers_hw2reg_ro_cache_end_mreg_t [3:0] ro_cache_end; // [127:0]
  } control_registers_hw2reg_t;

  // Register offsets
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_EOC_OFFSET = 9'h 0;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_WAKE_UP_OFFSET = 9'h 4;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_WAKE_UP_TILE_0_OFFSET = 9'h 8;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_WAKE_UP_TILE_1_OFFSET = 9'h c;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_WAKE_UP_TILE_2_OFFSET = 9'h 10;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_WAKE_UP_TILE_3_OFFSET = 9'h 14;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_WAKE_UP_TILE_4_OFFSET = 9'h 18;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_WAKE_UP_TILE_5_OFFSET = 9'h 1c;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_WAKE_UP_TILE_6_OFFSET = 9'h 20;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_WAKE_UP_TILE_7_OFFSET = 9'h 24;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_WAKE_UP_TILE_8_OFFSET = 9'h 28;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_WAKE_UP_TILE_9_OFFSET = 9'h 2c;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_WAKE_UP_TILE_10_OFFSET = 9'h 30;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_WAKE_UP_TILE_11_OFFSET = 9'h 34;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_WAKE_UP_TILE_12_OFFSET = 9'h 38;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_WAKE_UP_TILE_13_OFFSET = 9'h 3c;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_WAKE_UP_TILE_14_OFFSET = 9'h 40;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_WAKE_UP_TILE_15_OFFSET = 9'h 44;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_WAKE_UP_TILE_16_OFFSET = 9'h 48;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_WAKE_UP_TILE_17_OFFSET = 9'h 4c;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_WAKE_UP_TILE_18_OFFSET = 9'h 50;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_WAKE_UP_TILE_19_OFFSET = 9'h 54;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_WAKE_UP_TILE_20_OFFSET = 9'h 58;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_WAKE_UP_TILE_21_OFFSET = 9'h 5c;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_WAKE_UP_TILE_22_OFFSET = 9'h 60;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_WAKE_UP_TILE_23_OFFSET = 9'h 64;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_WAKE_UP_TILE_24_OFFSET = 9'h 68;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_WAKE_UP_TILE_25_OFFSET = 9'h 6c;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_WAKE_UP_TILE_26_OFFSET = 9'h 70;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_WAKE_UP_TILE_27_OFFSET = 9'h 74;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_WAKE_UP_TILE_28_OFFSET = 9'h 78;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_WAKE_UP_TILE_29_OFFSET = 9'h 7c;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_WAKE_UP_TILE_30_OFFSET = 9'h 80;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_WAKE_UP_TILE_31_OFFSET = 9'h 84;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_WAKE_UP_TILE_32_OFFSET = 9'h 88;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_WAKE_UP_TILE_33_OFFSET = 9'h 8c;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_WAKE_UP_TILE_34_OFFSET = 9'h 90;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_WAKE_UP_TILE_35_OFFSET = 9'h 94;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_WAKE_UP_TILE_36_OFFSET = 9'h 98;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_WAKE_UP_TILE_37_OFFSET = 9'h 9c;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_WAKE_UP_TILE_38_OFFSET = 9'h a0;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_WAKE_UP_TILE_39_OFFSET = 9'h a4;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_WAKE_UP_TILE_40_OFFSET = 9'h a8;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_WAKE_UP_TILE_41_OFFSET = 9'h ac;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_WAKE_UP_TILE_42_OFFSET = 9'h b0;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_WAKE_UP_TILE_43_OFFSET = 9'h b4;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_WAKE_UP_TILE_44_OFFSET = 9'h b8;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_WAKE_UP_TILE_45_OFFSET = 9'h bc;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_WAKE_UP_TILE_46_OFFSET = 9'h c0;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_WAKE_UP_TILE_47_OFFSET = 9'h c4;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_WAKE_UP_TILE_48_OFFSET = 9'h c8;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_WAKE_UP_TILE_49_OFFSET = 9'h cc;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_WAKE_UP_TILE_50_OFFSET = 9'h d0;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_WAKE_UP_TILE_51_OFFSET = 9'h d4;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_WAKE_UP_TILE_52_OFFSET = 9'h d8;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_WAKE_UP_TILE_53_OFFSET = 9'h dc;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_WAKE_UP_TILE_54_OFFSET = 9'h e0;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_WAKE_UP_TILE_55_OFFSET = 9'h e4;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_WAKE_UP_TILE_56_OFFSET = 9'h e8;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_WAKE_UP_TILE_57_OFFSET = 9'h ec;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_WAKE_UP_TILE_58_OFFSET = 9'h f0;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_WAKE_UP_TILE_59_OFFSET = 9'h f4;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_WAKE_UP_TILE_60_OFFSET = 9'h f8;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_WAKE_UP_TILE_61_OFFSET = 9'h fc;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_WAKE_UP_TILE_62_OFFSET = 9'h 100;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_WAKE_UP_TILE_63_OFFSET = 9'h 104;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_WAKE_UP_GROUP_OFFSET = 9'h 108;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_WAKE_UP_CLUSTER_OFFSET = 9'h 10c;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_TCDM_START_ADDRESS_OFFSET = 9'h 110;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_TCDM_END_ADDRESS_OFFSET = 9'h 114;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_NR_CORES_REG_OFFSET = 9'h 118;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_RO_CACHE_ENABLE_OFFSET = 9'h 11c;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_RO_CACHE_FLUSH_OFFSET = 9'h 120;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_RO_CACHE_START_0_OFFSET = 9'h 124;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_RO_CACHE_START_1_OFFSET = 9'h 128;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_RO_CACHE_START_2_OFFSET = 9'h 12c;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_RO_CACHE_START_3_OFFSET = 9'h 130;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_RO_CACHE_END_0_OFFSET = 9'h 134;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_RO_CACHE_END_1_OFFSET = 9'h 138;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_RO_CACHE_END_2_OFFSET = 9'h 13c;
  parameter logic [BlockAw-1:0] CONTROL_REGISTERS_RO_CACHE_END_3_OFFSET = 9'h 140;

  // Reset values for hwext registers and their fields
  parameter logic [31:0] CONTROL_REGISTERS_TCDM_START_ADDRESS_RESVAL = 32'h 0;
  parameter logic [31:0] CONTROL_REGISTERS_TCDM_END_ADDRESS_RESVAL = 32'h 0;
  parameter logic [31:0] CONTROL_REGISTERS_NR_CORES_REG_RESVAL = 32'h 0;
  parameter logic [31:0] CONTROL_REGISTERS_RO_CACHE_START_0_RESVAL = 32'h 0;
  parameter logic [31:0] CONTROL_REGISTERS_RO_CACHE_START_1_RESVAL = 32'h 0;
  parameter logic [31:0] CONTROL_REGISTERS_RO_CACHE_START_2_RESVAL = 32'h 0;
  parameter logic [31:0] CONTROL_REGISTERS_RO_CACHE_START_3_RESVAL = 32'h 0;
  parameter logic [31:0] CONTROL_REGISTERS_RO_CACHE_END_0_RESVAL = 32'h 0;
  parameter logic [31:0] CONTROL_REGISTERS_RO_CACHE_END_1_RESVAL = 32'h 0;
  parameter logic [31:0] CONTROL_REGISTERS_RO_CACHE_END_2_RESVAL = 32'h 0;
  parameter logic [31:0] CONTROL_REGISTERS_RO_CACHE_END_3_RESVAL = 32'h 0;

  // Register index
  typedef enum int {
    CONTROL_REGISTERS_EOC,
    CONTROL_REGISTERS_WAKE_UP,
    CONTROL_REGISTERS_WAKE_UP_TILE_0,
    CONTROL_REGISTERS_WAKE_UP_TILE_1,
    CONTROL_REGISTERS_WAKE_UP_TILE_2,
    CONTROL_REGISTERS_WAKE_UP_TILE_3,
    CONTROL_REGISTERS_WAKE_UP_TILE_4,
    CONTROL_REGISTERS_WAKE_UP_TILE_5,
    CONTROL_REGISTERS_WAKE_UP_TILE_6,
    CONTROL_REGISTERS_WAKE_UP_TILE_7,
    CONTROL_REGISTERS_WAKE_UP_TILE_8,
    CONTROL_REGISTERS_WAKE_UP_TILE_9,
    CONTROL_REGISTERS_WAKE_UP_TILE_10,
    CONTROL_REGISTERS_WAKE_UP_TILE_11,
    CONTROL_REGISTERS_WAKE_UP_TILE_12,
    CONTROL_REGISTERS_WAKE_UP_TILE_13,
    CONTROL_REGISTERS_WAKE_UP_TILE_14,
    CONTROL_REGISTERS_WAKE_UP_TILE_15,
    CONTROL_REGISTERS_WAKE_UP_TILE_16,
    CONTROL_REGISTERS_WAKE_UP_TILE_17,
    CONTROL_REGISTERS_WAKE_UP_TILE_18,
    CONTROL_REGISTERS_WAKE_UP_TILE_19,
    CONTROL_REGISTERS_WAKE_UP_TILE_20,
    CONTROL_REGISTERS_WAKE_UP_TILE_21,
    CONTROL_REGISTERS_WAKE_UP_TILE_22,
    CONTROL_REGISTERS_WAKE_UP_TILE_23,
    CONTROL_REGISTERS_WAKE_UP_TILE_24,
    CONTROL_REGISTERS_WAKE_UP_TILE_25,
    CONTROL_REGISTERS_WAKE_UP_TILE_26,
    CONTROL_REGISTERS_WAKE_UP_TILE_27,
    CONTROL_REGISTERS_WAKE_UP_TILE_28,
    CONTROL_REGISTERS_WAKE_UP_TILE_29,
    CONTROL_REGISTERS_WAKE_UP_TILE_30,
    CONTROL_REGISTERS_WAKE_UP_TILE_31,
    CONTROL_REGISTERS_WAKE_UP_TILE_32,
    CONTROL_REGISTERS_WAKE_UP_TILE_33,
    CONTROL_REGISTERS_WAKE_UP_TILE_34,
    CONTROL_REGISTERS_WAKE_UP_TILE_35,
    CONTROL_REGISTERS_WAKE_UP_TILE_36,
    CONTROL_REGISTERS_WAKE_UP_TILE_37,
    CONTROL_REGISTERS_WAKE_UP_TILE_38,
    CONTROL_REGISTERS_WAKE_UP_TILE_39,
    CONTROL_REGISTERS_WAKE_UP_TILE_40,
    CONTROL_REGISTERS_WAKE_UP_TILE_41,
    CONTROL_REGISTERS_WAKE_UP_TILE_42,
    CONTROL_REGISTERS_WAKE_UP_TILE_43,
    CONTROL_REGISTERS_WAKE_UP_TILE_44,
    CONTROL_REGISTERS_WAKE_UP_TILE_45,
    CONTROL_REGISTERS_WAKE_UP_TILE_46,
    CONTROL_REGISTERS_WAKE_UP_TILE_47,
    CONTROL_REGISTERS_WAKE_UP_TILE_48,
    CONTROL_REGISTERS_WAKE_UP_TILE_49,
    CONTROL_REGISTERS_WAKE_UP_TILE_50,
    CONTROL_REGISTERS_WAKE_UP_TILE_51,
    CONTROL_REGISTERS_WAKE_UP_TILE_52,
    CONTROL_REGISTERS_WAKE_UP_TILE_53,
    CONTROL_REGISTERS_WAKE_UP_TILE_54,
    CONTROL_REGISTERS_WAKE_UP_TILE_55,
    CONTROL_REGISTERS_WAKE_UP_TILE_56,
    CONTROL_REGISTERS_WAKE_UP_TILE_57,
    CONTROL_REGISTERS_WAKE_UP_TILE_58,
    CONTROL_REGISTERS_WAKE_UP_TILE_59,
    CONTROL_REGISTERS_WAKE_UP_TILE_60,
    CONTROL_REGISTERS_WAKE_UP_TILE_61,
    CONTROL_REGISTERS_WAKE_UP_TILE_62,
    CONTROL_REGISTERS_WAKE_UP_TILE_63,
    CONTROL_REGISTERS_WAKE_UP_GROUP,
    CONTROL_REGISTERS_WAKE_UP_CLUSTER,
    CONTROL_REGISTERS_TCDM_START_ADDRESS,
    CONTROL_REGISTERS_TCDM_END_ADDRESS,
    CONTROL_REGISTERS_NR_CORES_REG,
    CONTROL_REGISTERS_RO_CACHE_ENABLE,
    CONTROL_REGISTERS_RO_CACHE_FLUSH,
    CONTROL_REGISTERS_RO_CACHE_START_0,
    CONTROL_REGISTERS_RO_CACHE_START_1,
    CONTROL_REGISTERS_RO_CACHE_START_2,
    CONTROL_REGISTERS_RO_CACHE_START_3,
    CONTROL_REGISTERS_RO_CACHE_END_0,
    CONTROL_REGISTERS_RO_CACHE_END_1,
    CONTROL_REGISTERS_RO_CACHE_END_2,
    CONTROL_REGISTERS_RO_CACHE_END_3
  } control_registers_id_e;

  // Register width information to check illegal writes
  parameter logic [3:0] CONTROL_REGISTERS_PERMIT [81] = '{
    4'b 1111, // index[ 0] CONTROL_REGISTERS_EOC
    4'b 1111, // index[ 1] CONTROL_REGISTERS_WAKE_UP
    4'b 1111, // index[ 2] CONTROL_REGISTERS_WAKE_UP_TILE_0
    4'b 1111, // index[ 3] CONTROL_REGISTERS_WAKE_UP_TILE_1
    4'b 1111, // index[ 4] CONTROL_REGISTERS_WAKE_UP_TILE_2
    4'b 1111, // index[ 5] CONTROL_REGISTERS_WAKE_UP_TILE_3
    4'b 1111, // index[ 6] CONTROL_REGISTERS_WAKE_UP_TILE_4
    4'b 1111, // index[ 7] CONTROL_REGISTERS_WAKE_UP_TILE_5
    4'b 1111, // index[ 8] CONTROL_REGISTERS_WAKE_UP_TILE_6
    4'b 1111, // index[ 9] CONTROL_REGISTERS_WAKE_UP_TILE_7
    4'b 1111, // index[10] CONTROL_REGISTERS_WAKE_UP_TILE_8
    4'b 1111, // index[11] CONTROL_REGISTERS_WAKE_UP_TILE_9
    4'b 1111, // index[12] CONTROL_REGISTERS_WAKE_UP_TILE_10
    4'b 1111, // index[13] CONTROL_REGISTERS_WAKE_UP_TILE_11
    4'b 1111, // index[14] CONTROL_REGISTERS_WAKE_UP_TILE_12
    4'b 1111, // index[15] CONTROL_REGISTERS_WAKE_UP_TILE_13
    4'b 1111, // index[16] CONTROL_REGISTERS_WAKE_UP_TILE_14
    4'b 1111, // index[17] CONTROL_REGISTERS_WAKE_UP_TILE_15
    4'b 1111, // index[18] CONTROL_REGISTERS_WAKE_UP_TILE_16
    4'b 1111, // index[19] CONTROL_REGISTERS_WAKE_UP_TILE_17
    4'b 1111, // index[20] CONTROL_REGISTERS_WAKE_UP_TILE_18
    4'b 1111, // index[21] CONTROL_REGISTERS_WAKE_UP_TILE_19
    4'b 1111, // index[22] CONTROL_REGISTERS_WAKE_UP_TILE_20
    4'b 1111, // index[23] CONTROL_REGISTERS_WAKE_UP_TILE_21
    4'b 1111, // index[24] CONTROL_REGISTERS_WAKE_UP_TILE_22
    4'b 1111, // index[25] CONTROL_REGISTERS_WAKE_UP_TILE_23
    4'b 1111, // index[26] CONTROL_REGISTERS_WAKE_UP_TILE_24
    4'b 1111, // index[27] CONTROL_REGISTERS_WAKE_UP_TILE_25
    4'b 1111, // index[28] CONTROL_REGISTERS_WAKE_UP_TILE_26
    4'b 1111, // index[29] CONTROL_REGISTERS_WAKE_UP_TILE_27
    4'b 1111, // index[30] CONTROL_REGISTERS_WAKE_UP_TILE_28
    4'b 1111, // index[31] CONTROL_REGISTERS_WAKE_UP_TILE_29
    4'b 1111, // index[32] CONTROL_REGISTERS_WAKE_UP_TILE_30
    4'b 1111, // index[33] CONTROL_REGISTERS_WAKE_UP_TILE_31
    4'b 1111, // index[34] CONTROL_REGISTERS_WAKE_UP_TILE_32
    4'b 1111, // index[35] CONTROL_REGISTERS_WAKE_UP_TILE_33
    4'b 1111, // index[36] CONTROL_REGISTERS_WAKE_UP_TILE_34
    4'b 1111, // index[37] CONTROL_REGISTERS_WAKE_UP_TILE_35
    4'b 1111, // index[38] CONTROL_REGISTERS_WAKE_UP_TILE_36
    4'b 1111, // index[39] CONTROL_REGISTERS_WAKE_UP_TILE_37
    4'b 1111, // index[40] CONTROL_REGISTERS_WAKE_UP_TILE_38
    4'b 1111, // index[41] CONTROL_REGISTERS_WAKE_UP_TILE_39
    4'b 1111, // index[42] CONTROL_REGISTERS_WAKE_UP_TILE_40
    4'b 1111, // index[43] CONTROL_REGISTERS_WAKE_UP_TILE_41
    4'b 1111, // index[44] CONTROL_REGISTERS_WAKE_UP_TILE_42
    4'b 1111, // index[45] CONTROL_REGISTERS_WAKE_UP_TILE_43
    4'b 1111, // index[46] CONTROL_REGISTERS_WAKE_UP_TILE_44
    4'b 1111, // index[47] CONTROL_REGISTERS_WAKE_UP_TILE_45
    4'b 1111, // index[48] CONTROL_REGISTERS_WAKE_UP_TILE_46
    4'b 1111, // index[49] CONTROL_REGISTERS_WAKE_UP_TILE_47
    4'b 1111, // index[50] CONTROL_REGISTERS_WAKE_UP_TILE_48
    4'b 1111, // index[51] CONTROL_REGISTERS_WAKE_UP_TILE_49
    4'b 1111, // index[52] CONTROL_REGISTERS_WAKE_UP_TILE_50
    4'b 1111, // index[53] CONTROL_REGISTERS_WAKE_UP_TILE_51
    4'b 1111, // index[54] CONTROL_REGISTERS_WAKE_UP_TILE_52
    4'b 1111, // index[55] CONTROL_REGISTERS_WAKE_UP_TILE_53
    4'b 1111, // index[56] CONTROL_REGISTERS_WAKE_UP_TILE_54
    4'b 1111, // index[57] CONTROL_REGISTERS_WAKE_UP_TILE_55
    4'b 1111, // index[58] CONTROL_REGISTERS_WAKE_UP_TILE_56
    4'b 1111, // index[59] CONTROL_REGISTERS_WAKE_UP_TILE_57
    4'b 1111, // index[60] CONTROL_REGISTERS_WAKE_UP_TILE_58
    4'b 1111, // index[61] CONTROL_REGISTERS_WAKE_UP_TILE_59
    4'b 1111, // index[62] CONTROL_REGISTERS_WAKE_UP_TILE_60
    4'b 1111, // index[63] CONTROL_REGISTERS_WAKE_UP_TILE_61
    4'b 1111, // index[64] CONTROL_REGISTERS_WAKE_UP_TILE_62
    4'b 1111, // index[65] CONTROL_REGISTERS_WAKE_UP_TILE_63
    4'b 1111, // index[66] CONTROL_REGISTERS_WAKE_UP_GROUP
    4'b 1111, // index[67] CONTROL_REGISTERS_WAKE_UP_CLUSTER
    4'b 1111, // index[68] CONTROL_REGISTERS_TCDM_START_ADDRESS
    4'b 1111, // index[69] CONTROL_REGISTERS_TCDM_END_ADDRESS
    4'b 1111, // index[70] CONTROL_REGISTERS_NR_CORES_REG
    4'b 1111, // index[71] CONTROL_REGISTERS_RO_CACHE_ENABLE
    4'b 1111, // index[72] CONTROL_REGISTERS_RO_CACHE_FLUSH
    4'b 1111, // index[73] CONTROL_REGISTERS_RO_CACHE_START_0
    4'b 1111, // index[74] CONTROL_REGISTERS_RO_CACHE_START_1
    4'b 1111, // index[75] CONTROL_REGISTERS_RO_CACHE_START_2
    4'b 1111, // index[76] CONTROL_REGISTERS_RO_CACHE_START_3
    4'b 1111, // index[77] CONTROL_REGISTERS_RO_CACHE_END_0
    4'b 1111, // index[78] CONTROL_REGISTERS_RO_CACHE_END_1
    4'b 1111, // index[79] CONTROL_REGISTERS_RO_CACHE_END_2
    4'b 1111  // index[80] CONTROL_REGISTERS_RO_CACHE_END_3
  };

endpackage

