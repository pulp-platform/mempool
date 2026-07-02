#
# Copyright (C) 2020 ETH Zurich and University of Bologna
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#

# Author: Chi Zhang <chizhang@ethz.ch>

class FlexClusterArch:

    def __init__(self):

        #Cluster
        self.num_cluster_x           = 4
        self.num_cluster_y           = 4

        self.cluster_tcdm_base       = 0x00000000
        self.cluster_tcdm_size       = 0x00100000
        self.cluster_tcdm_remote     = 0x30000000

        self.cluster_stack_base      = 0x10000000
        self.cluster_stack_size      = 0x00020000

        self.cluster_reg_base        = 0x20000000
        self.cluster_reg_size        = 0x00000200

        self.instruction_mem_base    = 0x80000000

        # Mempool cluster configuration (Mempool)
        self.terapool                    = False
        self.num_core_per_cluster        = 256
        self.nb_cores_per_tile           = 4
        self.nb_sub_groups_per_group     = 1
        self.nb_groups                   = 4
        self.bank_factor                 = 4
        self.bank_size                   = 1024
        self.axi_data_width              = 64
        self.nb_axi_masters_per_group    = 1
        self.instruction_mem_size        = 0x400000
        self.nb_l2_banks                 = 4

        # Tensor engines (RedMulE) -- disabled for this preset
        self.tensorpool                  = False
        self.nb_redmule_tiles            = 0
        self.redmule_height              = 0
        self.redmule_width               = 0
        self.redmule_regs                = 0

        #HBM
        self.hbm_start_base          = 0xc0000000
        self.hbm_node_addr_space     = 0x00200000
        self.num_node_per_ctrl       = 1
        self.hbm_chan_placement      = [4,0,0,0]
        self.hbm_node_aliase         = 1

        #NoC
        self.noc_outstanding         = 64
        self.noc_link_width          = 512

        #System
        self.soc_register_base       = 0x90000000
        self.soc_register_size       = 0x00010000
        self.soc_register_eoc        = 0x90000000
        self.soc_register_wakeup     = 0x90000004

        #Synchronization
        self.sync_base               = 0x50000000
        self.sync_interleave         = 0x00000080
        self.sync_special_mem        = 0x00000040
