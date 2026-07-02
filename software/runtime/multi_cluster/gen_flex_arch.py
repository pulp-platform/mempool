#!/usr/bin/env python3
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
#
# Generate the C (flex_cluster_arch.h) and assembly (flex_cluster_arch.inc)
# FlexCluster architecture headers from a SoftHier `FlexClusterArch` config.
# Ported from soft_hier/flex_cluster_utilities/config.py with configurable
# input/output paths so it can be driven by the MemPool multi_cluster build.

import re
import ast
import os
import math
import argparse


def write_if_changed(path, content):
    """Only (over)write the file when its content actually changes, so that
    rebuilding with an unchanged `config` does not touch the header's mtime
    and trigger needless recompilation of the whole runtime."""
    if os.path.exists(path):
        with open(path, 'r') as existing:
            if existing.read() == content:
                print(f'Header file "{path}" already up to date.')
                return
    with open(path, 'w') as file:
        file.write(content)
    print(f'Header file "{path}" generated successfully.')

parser = argparse.ArgumentParser(
    description="Generate C and S header files from a SoftHier configuration file.")
parser.add_argument("input_file", help="Path to the input Python config file")
parser.add_argument("--outdir", default=os.path.join(os.path.dirname(os.path.abspath(__file__)), "include"),
                    help="Directory where the generated headers are written")
args = parser.parse_args()
input_file = args.input_file

C_header_file = os.path.join(args.outdir, 'flex_cluster_arch.h')
S_header_file = os.path.join(args.outdir, 'flex_cluster_arch.inc')

# Initialize a dictionary to store the class attributes and their values
attributes = {}

# Read the input file and extract the class attributes
with open(input_file, 'r') as file:
    lines = file.readlines()
    for line in lines:
        match = re.match(r'\s*self\.(\w+)\s*=\s*(.+)', line)
        if match:
            attr_name = match.group(1)
            attr_value = match.group(2)
            attributes[attr_name] = attr_value

# Build the output C header file
c_header = '#ifndef FLEXCLUSTERARCH_H\n'
c_header += '#define FLEXCLUSTERARCH_H\n\n'
num_core_per_cluster = 0

for attr_name, attr_value in attributes.items():
    # Convert attribute name to uppercase and prefix with 'ARCH_'
    define_name = f'ARCH_{attr_name.upper()}'
    if define_name == 'ARCH_NUM_CORE_PER_CLUSTER':
        num_core_per_cluster = int(attr_value)
        pass
    if define_name == 'ARCH_SPATZ_ATTACED_CORE_LIST':
        core_list = ast.literal_eval(attr_value)
        c_header += f'#define ARCH_SPATZ_ATTACED_CORES {len(core_list)}\n'
        attach_list = []
        sid_list = []
        sid = 0
        for x in range(num_core_per_cluster):
            if x in core_list:
                attach_list.append(1)
                sid_list.append(sid)
                sid = sid + 1
            else:
                attach_list.append(0)
                sid_list.append(0)
                pass
            pass
        attach_list_str = str(attach_list).replace("[", "{").replace("]", "}")
        c_header += f'#define ARCH_SPATZ_ATTACED_CHECK_LIST {attach_list_str}\n'
        sid_list_str = str(sid_list).replace("[", "{").replace("]", "}")
        c_header += f'#define ARCH_SPATZ_ATTACED_SID_LIST {sid_list_str}\n'
        attr_value = attr_value.replace("[", "{").replace("]", "}")
        pass
    c_header += f'#define {define_name} {attr_value}\n'

c_header += '\n#endif // FLEXCLUSTERARCH_H\n'
write_if_changed(C_header_file, c_header)

# Build the output S header file
s_header = '#ifndef FLEXCLUSTERARCH_H\n'
s_header += '#define FLEXCLUSTERARCH_H\n\n'
num_core_per_cluster = 0

for attr_name, attr_value in attributes.items():
    # Convert attribute name to uppercase and prefix with 'ARCH_'
    define_name = f'ARCH_{attr_name.upper()}'
    if define_name == 'ARCH_NUM_CORE_PER_CLUSTER':
        num_core_per_cluster = int(attr_value)
        pass
    if define_name == 'ARCH_HBM_CHAN_PLACEMENT' or define_name == 'ARCH_SPATZ_ATTACED_CORE_LIST' or define_name == 'ARCH_HBM_TYPE':
        continue
        pass
    if define_name == 'ARCH_CLUSTER_STACK_SIZE':
        clog2_stack_offest_per_core = int(math.ceil(math.log2(int(attr_value, 16)/(1 << (num_core_per_cluster - 1).bit_length()))))
        s_header += f'.set ARCH_CLUSTER_STACK_OFFSET, {clog2_stack_offest_per_core}\n'
        pass
    s_header += f'.set {define_name}, {attr_value}\n'

s_header += '\n#endif // FLEXCLUSTERARCH_H\n'
write_if_changed(S_header_file, s_header)
