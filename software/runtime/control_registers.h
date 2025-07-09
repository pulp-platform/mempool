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
#define CONTROL_REGISTERS_PARAM_MAX_NUMGROUPS 8

// Register width
#define CONTROL_REGISTERS_PARAM_REG_WIDTH 32

// End-of-Computation Register
#define CONTROL_REGISTERS_EOC_REG_OFFSET 0x0

// Wake Up Register
#define CONTROL_REGISTERS_WAKE_UP_REG_OFFSET 0x4

// Wake Up Tile Register (common parameters)
#define CONTROL_REGISTERS_WAKE_UP_TILE_WAKE_UP_TILE_FIELD_WIDTH 32
#define CONTROL_REGISTERS_WAKE_UP_TILE_WAKE_UP_TILE_FIELDS_PER_REG 1
#define CONTROL_REGISTERS_WAKE_UP_TILE_MULTIREG_COUNT 8

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

// Wake Up Group Register
#define CONTROL_REGISTERS_WAKE_UP_GROUP_REG_OFFSET 0x28

// TCDM Start Address Register
#define CONTROL_REGISTERS_TCDM_START_ADDRESS_REG_OFFSET 0x2c

// TCDM End Address Register
#define CONTROL_REGISTERS_TCDM_END_ADDRESS_REG_OFFSET 0x30

// Number of Cores Register
#define CONTROL_REGISTERS_NR_CORES_REG_REG_OFFSET 0x34

// Read-only cache Enable
#define CONTROL_REGISTERS_RO_CACHE_ENABLE_REG_OFFSET 0x38

// Read-only cache Flush
#define CONTROL_REGISTERS_RO_CACHE_FLUSH_REG_OFFSET 0x3c

// Read-only cache Region Start (common parameters)
#define CONTROL_REGISTERS_RO_CACHE_START_RO_CACHE_START_FIELD_WIDTH 32
#define CONTROL_REGISTERS_RO_CACHE_START_RO_CACHE_START_FIELDS_PER_REG 1
#define CONTROL_REGISTERS_RO_CACHE_START_MULTIREG_COUNT 4

// Read-only cache Region Start
#define CONTROL_REGISTERS_RO_CACHE_START_0_REG_OFFSET 0x40

// Read-only cache Region Start
#define CONTROL_REGISTERS_RO_CACHE_START_1_REG_OFFSET 0x44

// Read-only cache Region Start
#define CONTROL_REGISTERS_RO_CACHE_START_2_REG_OFFSET 0x48

// Read-only cache Region Start
#define CONTROL_REGISTERS_RO_CACHE_START_3_REG_OFFSET 0x4c

// Read-only cache Region End (common parameters)
#define CONTROL_REGISTERS_RO_CACHE_END_RO_CACHE_END_FIELD_WIDTH 32
#define CONTROL_REGISTERS_RO_CACHE_END_RO_CACHE_END_FIELDS_PER_REG 1
#define CONTROL_REGISTERS_RO_CACHE_END_MULTIREG_COUNT 4

// Read-only cache Region End
#define CONTROL_REGISTERS_RO_CACHE_END_0_REG_OFFSET 0x50

// Read-only cache Region End
#define CONTROL_REGISTERS_RO_CACHE_END_1_REG_OFFSET 0x54

// Read-only cache Region End
#define CONTROL_REGISTERS_RO_CACHE_END_2_REG_OFFSET 0x58

// Read-only cache Region End
#define CONTROL_REGISTERS_RO_CACHE_END_3_REG_OFFSET 0x5c

#ifdef __cplusplus
} // extern "C"
#endif
#endif // _CONTROL_REGISTERS_REG_DEFS_
       // End generated register defines for control_registers