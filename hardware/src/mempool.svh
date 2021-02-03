// Copyright (c) 2021 ETH Zurich, University of Bologna
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Macros used throughout the MemPool project

`ifndef MEMPOOL_SVH_
`define MEMPOOL_SVH_

  // Structs in ports of hierarchical modules are not supported in Verilator
  // --> Flatten them for Verilator
  `define STRUCT_PORT(struct_t)  \
  `ifndef VERILATOR              \
    struct_t                     \
  `else                          \
    logic[$bits(struct_t)-1:0]   \
  `endif

  // Create a flattened vector of a struct. Make sure the first dimension is
  // the dimension into the vector of struct types and not the struct itself.
  `define STRUCT_VECT(struct_t, dim)  \
  `ifndef VERILATOR                   \
    struct_t dim                      \
  `else                               \
    logic dim [$bits(struct_t)-1:0]   \
  `endif

`endif
