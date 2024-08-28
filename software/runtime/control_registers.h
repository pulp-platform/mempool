// Generated register defines for control_registers

// Copyright information found in source file:
// Copyright 2024 ETH Zurich and University of Bologna.

// Licensing information found in source file:
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

#ifndef _CONTROL_REGISTERS_REG_DEFS_
#define _CONTROL_REGISTERS_REG_DEFS_

#ifdef __cplusplus
extern "C" {
#endif
// Number of programmable address regions for the read-only cache
#define CONTROL_REGISTERS_PARAM_R_O_CACHE_NUM_ADDR_RULES 4

// Maximum number of groups that we support in any configuration
#define CONTROL_REGISTERS_PARAM_MAX_NUMGROUPS 64

// Register width
#define CONTROL_REGISTERS_PARAM_REG_WIDTH 32

// End-of-Computation Register
#define CONTROL_REGISTERS_EOC_REG_OFFSET 0x0

// Wake Up Register
#define CONTROL_REGISTERS_WAKE_UP_REG_OFFSET 0x4

// Wake Up Tile Register (common parameters)
#define CONTROL_REGISTERS_WAKE_UP_TILE_WAKE_UP_TILE_FIELD_WIDTH 32
#define CONTROL_REGISTERS_WAKE_UP_TILE_WAKE_UP_TILE_FIELDS_PER_REG 1
#define CONTROL_REGISTERS_WAKE_UP_TILE_MULTIREG_COUNT 64

// Wake Up Tile Register
#define CONTROL_REGISTERS_WAKE_UP_TILE_0_REG_OFFSET 0x8

// Wake Up Tile Register
#define CONTROL_REGISTERS_WAKE_UP_TILE_1_REG_OFFSET 0xc

// Wake Up Tile Register
#define CONTROL_REGISTERS_WAKE_UP_TILE_2_REG_OFFSET 0x10

// Wake Up Tile Register
#define CONTROL_REGISTERS_WAKE_UP_TILE_3_REG_OFFSET 0x14

// Wake Up Tile Register
#define CONTROL_REGISTERS_WAKE_UP_TILE_4_REG_OFFSET 0x18

// Wake Up Tile Register
#define CONTROL_REGISTERS_WAKE_UP_TILE_5_REG_OFFSET 0x1c

// Wake Up Tile Register
#define CONTROL_REGISTERS_WAKE_UP_TILE_6_REG_OFFSET 0x20

// Wake Up Tile Register
#define CONTROL_REGISTERS_WAKE_UP_TILE_7_REG_OFFSET 0x24

// Wake Up Tile Register
#define CONTROL_REGISTERS_WAKE_UP_TILE_8_REG_OFFSET 0x28

// Wake Up Tile Register
#define CONTROL_REGISTERS_WAKE_UP_TILE_9_REG_OFFSET 0x2c

// Wake Up Tile Register
#define CONTROL_REGISTERS_WAKE_UP_TILE_10_REG_OFFSET 0x30

// Wake Up Tile Register
#define CONTROL_REGISTERS_WAKE_UP_TILE_11_REG_OFFSET 0x34

// Wake Up Tile Register
#define CONTROL_REGISTERS_WAKE_UP_TILE_12_REG_OFFSET 0x38

// Wake Up Tile Register
#define CONTROL_REGISTERS_WAKE_UP_TILE_13_REG_OFFSET 0x3c

// Wake Up Tile Register
#define CONTROL_REGISTERS_WAKE_UP_TILE_14_REG_OFFSET 0x40

// Wake Up Tile Register
#define CONTROL_REGISTERS_WAKE_UP_TILE_15_REG_OFFSET 0x44

// Wake Up Tile Register
#define CONTROL_REGISTERS_WAKE_UP_TILE_16_REG_OFFSET 0x48

// Wake Up Tile Register
#define CONTROL_REGISTERS_WAKE_UP_TILE_17_REG_OFFSET 0x4c

// Wake Up Tile Register
#define CONTROL_REGISTERS_WAKE_UP_TILE_18_REG_OFFSET 0x50

// Wake Up Tile Register
#define CONTROL_REGISTERS_WAKE_UP_TILE_19_REG_OFFSET 0x54

// Wake Up Tile Register
#define CONTROL_REGISTERS_WAKE_UP_TILE_20_REG_OFFSET 0x58

// Wake Up Tile Register
#define CONTROL_REGISTERS_WAKE_UP_TILE_21_REG_OFFSET 0x5c

// Wake Up Tile Register
#define CONTROL_REGISTERS_WAKE_UP_TILE_22_REG_OFFSET 0x60

// Wake Up Tile Register
#define CONTROL_REGISTERS_WAKE_UP_TILE_23_REG_OFFSET 0x64

// Wake Up Tile Register
#define CONTROL_REGISTERS_WAKE_UP_TILE_24_REG_OFFSET 0x68

// Wake Up Tile Register
#define CONTROL_REGISTERS_WAKE_UP_TILE_25_REG_OFFSET 0x6c

// Wake Up Tile Register
#define CONTROL_REGISTERS_WAKE_UP_TILE_26_REG_OFFSET 0x70

// Wake Up Tile Register
#define CONTROL_REGISTERS_WAKE_UP_TILE_27_REG_OFFSET 0x74

// Wake Up Tile Register
#define CONTROL_REGISTERS_WAKE_UP_TILE_28_REG_OFFSET 0x78

// Wake Up Tile Register
#define CONTROL_REGISTERS_WAKE_UP_TILE_29_REG_OFFSET 0x7c

// Wake Up Tile Register
#define CONTROL_REGISTERS_WAKE_UP_TILE_30_REG_OFFSET 0x80

// Wake Up Tile Register
#define CONTROL_REGISTERS_WAKE_UP_TILE_31_REG_OFFSET 0x84

// Wake Up Tile Register
#define CONTROL_REGISTERS_WAKE_UP_TILE_32_REG_OFFSET 0x88

// Wake Up Tile Register
#define CONTROL_REGISTERS_WAKE_UP_TILE_33_REG_OFFSET 0x8c

// Wake Up Tile Register
#define CONTROL_REGISTERS_WAKE_UP_TILE_34_REG_OFFSET 0x90

// Wake Up Tile Register
#define CONTROL_REGISTERS_WAKE_UP_TILE_35_REG_OFFSET 0x94

// Wake Up Tile Register
#define CONTROL_REGISTERS_WAKE_UP_TILE_36_REG_OFFSET 0x98

// Wake Up Tile Register
#define CONTROL_REGISTERS_WAKE_UP_TILE_37_REG_OFFSET 0x9c

// Wake Up Tile Register
#define CONTROL_REGISTERS_WAKE_UP_TILE_38_REG_OFFSET 0xa0

// Wake Up Tile Register
#define CONTROL_REGISTERS_WAKE_UP_TILE_39_REG_OFFSET 0xa4

// Wake Up Tile Register
#define CONTROL_REGISTERS_WAKE_UP_TILE_40_REG_OFFSET 0xa8

// Wake Up Tile Register
#define CONTROL_REGISTERS_WAKE_UP_TILE_41_REG_OFFSET 0xac

// Wake Up Tile Register
#define CONTROL_REGISTERS_WAKE_UP_TILE_42_REG_OFFSET 0xb0

// Wake Up Tile Register
#define CONTROL_REGISTERS_WAKE_UP_TILE_43_REG_OFFSET 0xb4

// Wake Up Tile Register
#define CONTROL_REGISTERS_WAKE_UP_TILE_44_REG_OFFSET 0xb8

// Wake Up Tile Register
#define CONTROL_REGISTERS_WAKE_UP_TILE_45_REG_OFFSET 0xbc

// Wake Up Tile Register
#define CONTROL_REGISTERS_WAKE_UP_TILE_46_REG_OFFSET 0xc0

// Wake Up Tile Register
#define CONTROL_REGISTERS_WAKE_UP_TILE_47_REG_OFFSET 0xc4

// Wake Up Tile Register
#define CONTROL_REGISTERS_WAKE_UP_TILE_48_REG_OFFSET 0xc8

// Wake Up Tile Register
#define CONTROL_REGISTERS_WAKE_UP_TILE_49_REG_OFFSET 0xcc

// Wake Up Tile Register
#define CONTROL_REGISTERS_WAKE_UP_TILE_50_REG_OFFSET 0xd0

// Wake Up Tile Register
#define CONTROL_REGISTERS_WAKE_UP_TILE_51_REG_OFFSET 0xd4

// Wake Up Tile Register
#define CONTROL_REGISTERS_WAKE_UP_TILE_52_REG_OFFSET 0xd8

// Wake Up Tile Register
#define CONTROL_REGISTERS_WAKE_UP_TILE_53_REG_OFFSET 0xdc

// Wake Up Tile Register
#define CONTROL_REGISTERS_WAKE_UP_TILE_54_REG_OFFSET 0xe0

// Wake Up Tile Register
#define CONTROL_REGISTERS_WAKE_UP_TILE_55_REG_OFFSET 0xe4

// Wake Up Tile Register
#define CONTROL_REGISTERS_WAKE_UP_TILE_56_REG_OFFSET 0xe8

// Wake Up Tile Register
#define CONTROL_REGISTERS_WAKE_UP_TILE_57_REG_OFFSET 0xec

// Wake Up Tile Register
#define CONTROL_REGISTERS_WAKE_UP_TILE_58_REG_OFFSET 0xf0

// Wake Up Tile Register
#define CONTROL_REGISTERS_WAKE_UP_TILE_59_REG_OFFSET 0xf4

// Wake Up Tile Register
#define CONTROL_REGISTERS_WAKE_UP_TILE_60_REG_OFFSET 0xf8

// Wake Up Tile Register
#define CONTROL_REGISTERS_WAKE_UP_TILE_61_REG_OFFSET 0xfc

// Wake Up Tile Register
#define CONTROL_REGISTERS_WAKE_UP_TILE_62_REG_OFFSET 0x100

// Wake Up Tile Register
#define CONTROL_REGISTERS_WAKE_UP_TILE_63_REG_OFFSET 0x104

// Wake Up Group Register
#define CONTROL_REGISTERS_WAKE_UP_GROUP_REG_OFFSET 0x108

// Wake Up Cluster Register
#define CONTROL_REGISTERS_WAKE_UP_CLUSTER_REG_OFFSET 0x10c

// TCDM Start Address Register
#define CONTROL_REGISTERS_TCDM_START_ADDRESS_REG_OFFSET 0x110

// TCDM End Address Register
#define CONTROL_REGISTERS_TCDM_END_ADDRESS_REG_OFFSET 0x114

// Number of Cores Register
#define CONTROL_REGISTERS_NR_CORES_REG_REG_OFFSET 0x118

// Read-only cache Enable
#define CONTROL_REGISTERS_RO_CACHE_ENABLE_REG_OFFSET 0x11c

// Read-only cache Flush
#define CONTROL_REGISTERS_RO_CACHE_FLUSH_REG_OFFSET 0x120

// Read-only cache Region Start (common parameters)
#define CONTROL_REGISTERS_RO_CACHE_START_RO_CACHE_START_FIELD_WIDTH 32
#define CONTROL_REGISTERS_RO_CACHE_START_RO_CACHE_START_FIELDS_PER_REG 1
#define CONTROL_REGISTERS_RO_CACHE_START_MULTIREG_COUNT 4

// Read-only cache Region Start
#define CONTROL_REGISTERS_RO_CACHE_START_0_REG_OFFSET 0x124

// Read-only cache Region Start
#define CONTROL_REGISTERS_RO_CACHE_START_1_REG_OFFSET 0x128

// Read-only cache Region Start
#define CONTROL_REGISTERS_RO_CACHE_START_2_REG_OFFSET 0x12c

// Read-only cache Region Start
#define CONTROL_REGISTERS_RO_CACHE_START_3_REG_OFFSET 0x130

// Read-only cache Region End (common parameters)
#define CONTROL_REGISTERS_RO_CACHE_END_RO_CACHE_END_FIELD_WIDTH 32
#define CONTROL_REGISTERS_RO_CACHE_END_RO_CACHE_END_FIELDS_PER_REG 1
#define CONTROL_REGISTERS_RO_CACHE_END_MULTIREG_COUNT 4

// Read-only cache Region End
#define CONTROL_REGISTERS_RO_CACHE_END_0_REG_OFFSET 0x134

// Read-only cache Region End
#define CONTROL_REGISTERS_RO_CACHE_END_1_REG_OFFSET 0x138

// Read-only cache Region End
#define CONTROL_REGISTERS_RO_CACHE_END_2_REG_OFFSET 0x13c

// Read-only cache Region End
#define CONTROL_REGISTERS_RO_CACHE_END_3_REG_OFFSET 0x140

#ifdef __cplusplus
}  // extern "C"
#endif
#endif  // _CONTROL_REGISTERS_REG_DEFS_
// End generated register defines for control_registers