// Copyright 2023 ETH Zurich and University of Bologna.
//
// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//    http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// Author: Sergio Mazzola, ETH Zurich

// Hardware
#define NUM_QUEUES_PER_CORE BANKING_FACTOR

// QLR CSR addresses
#define QLR_CFG_T0 (QLR_CFG_BASE | (5 << 5))
#define QLR_CFG_T1 (QLR_CFG_BASE | (6 << 5))
#define QLR_CFG_T2 (QLR_CFG_BASE | (7 << 5))
#define QLR_CFG_T3 (QLR_CFG_BASE | (28 << 5))

// QLR CSR bitfields
#define QLR_CFG_TYPE  0 // type of QLR (0=off, 1=IQLR, 2=OQLR, 3=IOQLR)
#define QLR_CFG_REQ   2 // num of requests before QLR turns off again
#define QLR_CFG_RF    3 // num of register reads before I[O]QLR is updated
#define QLR_CFG_IADDR 4 // memory bank index of I[O]QLR input queue
#define QLR_CFG_OADDR 5 // memory bank index of [I]OQLR output queue

// QLR "Type" configuration values
#define QLR_TYPE_OFF   0
#define QLR_TYPE_IQLR  1
#define QLR_TYPE_OQLR  2
#define QLR_TYPE_IOQLR 3

// QLRs (temporary registers according to RISC-V calling convention)
// https://riscv.org/wp-content/uploads/2015/01/riscv-calling.pdf
// Compile with -ffixed-x5 -ffixed-x6 -ffixed-x7 -ffixed-x28
register int32_t qlr_t0 asm("t0");
register int32_t qlr_t1 asm("t1");
register int32_t qlr_t2 asm("t2");
register int32_t qlr_t3 asm("t3");
