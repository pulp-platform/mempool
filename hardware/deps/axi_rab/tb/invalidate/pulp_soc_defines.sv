// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

`ifndef PULP_SOC_DEFINES_SV
`define PULP_SOC_DEFINES_SV

// RAB defines
`define AXI_EXT_ADDR_WIDTH    32
`define AXI_LITE_DATA_WIDTH   32
`define EN_L2TLB_ARRAY      {1,0} // Port 1, Port 0
`define N_SLICES_ARRAY     {32,4}
`define N_SLICES_MAX          32
`define EN_ACP                 1
// `define RAB_AX_LOG_EN          1
// `define RAB_AX_LOG_ENTRIES     2*1024
`define RAB_N_PORTS              2
`define RAB_L2_N_SETS           32
`define RAB_L2_N_SET_ENTRIES    32
`define RAB_L2_N_PAR_VA_RAMS     4

// Auxiliary defines
`define PAGE_SIZE             4096

`endif // PULP_SOC_DEFINES|SV
