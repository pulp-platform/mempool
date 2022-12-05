#!/usr/bin/env python3

# Copyright 2021 ETH Zurich and University of Bologna.
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51

# This script takes a simulation log dumping each core's queue addresses
# (i.e. the systolic array configuration) through the dump(name, reg)
# in software/runtime/runtime.h and builds a human readbale output

# Author: Sergio Mazzola <smazzola@iis.ee.ethz.ch>

import argparse
import sys
import os
import re
import pandas as pd
from collections import namedtuple
from math import log2

# ----------------- Architecture info -----------------

NUM_CORES = int(os.environ.get('num_cores', 256))
NUM_CORES_PER_TILE = int(os.environ.get('num_cores_per_tile', 4))
BANKING_FACTOR = int(os.environ.get('banking_factor', 4))
NUM_TILES = int(NUM_CORES / NUM_CORES_PER_TILE)
NUM_GROUPS = int(os.environ.get('num_groups', 4))
SEQ_MEM_SIZE_TILE = NUM_CORES_PER_TILE * int(os.environ.get('seq_mem_size', 2048))
BANK_SIZE = 1024
NUM_BANKS_PER_TILE = BANKING_FACTOR * NUM_CORES_PER_TILE
TCDM_SIZE = NUM_BANKS_PER_TILE * BANK_SIZE * NUM_TILES
ADDR_BYTE_OFFSET = 2
ADDR_WIDTH = 32

# ----------------- Parameters -----------------

OUTPUT_CSV = '../build/queues.csv'

# Expects a log file including the following content:

# ...
# [UART] [QUEUE] queue_name
# [DUMP]  hart_id: csr_hex = value_hex,  value_dec
# [DUMP]  hart_id: csr_hex = value_hex,  value_dec
# [DUMP]  hart_id: csr_hex = value_hex,  value_dec
# ...

queue_regexp = re.compile(r'^.*\[QUEUE\]\s+(.*)$')
dump_regexp = re.compile(r'^\[DUMP\]\s+[0-9]+: 0x[0-9a-fA-F]+ = (0x[0-9a-fA-F]+),\s+([0-9]+)$')

systolic_entry_raw = namedtuple('systolic_entry_raw', 'core_id xqueue address')
systolic_pe = namedtuple('systolic_entry', 'xqueue tile_id core_id queue_tile_pop queue_bank_pop queue_tile_push queue_bank_push addr_pop addr_push')
routing = namedtuple('routing', 'address_dec address_hex tile_id bank_id row_i')

# ----------------- Helper functions -----------------

def int2bin(integer: int) -> str:
    # convert to bin and reverse to allow systemverilog-like indexing
    binary = bin(integer)[2:]
    return binary[::-1].ljust(32, '0')

def bin2int(binary: str) -> int:
    return int(binary[::-1], 2)

def int2hex(integer: int) -> str:
    # convert to hex with 8 hexadecimal digits
    hex_digits = 8
    return "{0:#0{1}x}".format(integer, hex_digits + 2)

# ----------------- Architectural models -----------------

def address_scrambler(address_dec_in: int) -> int:
    address_bin = int2bin(address_dec_in)
    # directly from address_scrambler.sv
    byte_offset = ADDR_BYTE_OFFSET
    bank_offset_bits = (NUM_BANKS_PER_TILE - 1).bit_length()
    tile_id_bits = (NUM_TILES - 1).bit_length()
    seq_per_tile_bits = (SEQ_MEM_SIZE_TILE - 1).bit_length()
    seq_total_bits = seq_per_tile_bits+tile_id_bits
    constant_bits = byte_offset + bank_offset_bits
    scramble_bits = seq_per_tile_bits-constant_bits
    # scramble if in sequential memory region
    if address_dec_in < SEQ_MEM_SIZE_TILE * NUM_TILES:
        address_bin = address_bin[:constant_bits] + address_bin[seq_per_tile_bits:seq_total_bits] + \
            address_bin[constant_bits:seq_per_tile_bits] + address_bin[seq_per_tile_bits:]
    return bin2int(address_bin)

def core2tile_id(core_id: int) -> int:
    return int(core_id/NUM_CORES_PER_TILE)

def addr2routing(address_dec_in: int):
    # directly from address_scrambler.sv
    byte_offset = ADDR_BYTE_OFFSET
    bank_offset_bits = (NUM_BANKS_PER_TILE - 1).bit_length()
    tile_id_bits = (NUM_TILES - 1).bit_length()
    # masks
    bank_mask = NUM_BANKS_PER_TILE-1
    tile_mask = NUM_TILES-1
    row_mask = 2**(ADDR_WIDTH - byte_offset - bank_offset_bits - tile_id_bits) - 1
    # scramble
    address = address_scrambler(address_dec_in)
    # compute
    bank_id = (address >> byte_offset) & bank_mask
    tile_id = (address >> (byte_offset + bank_offset_bits)) & tile_mask
    row_i = (address >> (byte_offset + bank_offset_bits + tile_id_bits)) & row_mask
    return routing(
        address_dec = address,
        address_hex = int2hex(address),
        tile_id = tile_id,
        bank_id = bank_id,
        row_i = row_i
    )

# ----------------- Systolic mappings -----------------

def systolic_map_conv2d(map_raw: list):
    map_elab = []
    map_raw_dict = {(e.core_id, e.xqueue):e.address for e in map_raw}
    for e in map_raw:
        # elaborate data
        core_id = e.core_id
        xqueue = e.xqueue
        tile_id = core2tile_id(core_id)
        if core_id == 0:
            addr_pop = None
            addr_push = map_raw_dict[(core_id + 1, xqueue)]
            bank_push = addr2routing(addr_push)
            queue_tile_pop = None
            queue_bank_pop = None
            queue_tile_push = bank_push.tile_id
            queue_bank_push = bank_push.bank_id
            addr_push = int2hex(addr_push)
        elif core_id == (NUM_CORES-1):
            addr_pop = e.address
            addr_push = None
            bank_pop = addr2routing(addr_pop)
            queue_tile_pop = bank_pop.tile_id
            queue_bank_pop = bank_pop.bank_id
            queue_tile_push = None
            queue_bank_push = None
            addr_pop = int2hex(addr_pop)
        else:
            addr_pop = e.address
            addr_push = map_raw_dict[(core_id + 1, xqueue)]
            bank_pop = addr2routing(addr_pop)
            bank_push = addr2routing(addr_push)
            queue_tile_pop = bank_pop.tile_id
            queue_bank_pop = bank_pop.bank_id
            queue_tile_push = bank_push.tile_id
            queue_bank_push = bank_push.bank_id
            addr_pop = int2hex(addr_pop)
            addr_push = int2hex(addr_push)
        # append new element
        map_elab.append(
            systolic_pe(
                xqueue = e.xqueue,
                tile_id = tile_id,
                core_id = core_id,
                queue_tile_pop = queue_tile_pop,
                queue_bank_pop = queue_bank_pop,
                queue_tile_push = queue_tile_push,
                queue_bank_push = queue_bank_push,
                addr_pop = addr_pop,
                addr_push = addr_push
            )
        )
    return map_elab

# -------------------- Main --------------------

def main():
    # Argument parsing and iterator creation
    parser = argparse.ArgumentParser(
        description='Produce human readable core-queues map from a simulation log dumping queue addresses via CSRs'
    )
    parser.add_argument(
        'infile',
        metavar='sim.log',
        nargs='?',
        type=argparse.FileType('r'),
        default='./sim.log',
        help='A simulation log containing CSRs dumps with queues addresses',
    )
    args = parser.parse_args()
    log_file = args.infile
    log_path = args.infile.name

    # Parse log to obtain PE's raw mapping data
    map_raw = []
    parser_state = 0 # reset
    # Parser FSM
    for line in log_file:
        # still looking for queue dump line [QUEUE]
        if parser_state == 0:
            queue_name = re.findall(queue_regexp, line)
            core_id = 0
            if queue_name:
                parser_state = 1
        # queue dump found, but still no meaningful line; looking for [DUMP]
        elif parser_state == 1:
            csr_dump = re.findall(dump_regexp, line)
            if csr_dump:
                parser_state = 2
        # dump started, stop parsing as soon as one line is not a dump
        elif parser_state == 2:
            map_raw.append(
                systolic_entry_raw(
                    core_id = core_id,
                    xqueue = queue_name[0],
                    address = int(csr_dump[0][1])
                )
            )
            core_id = core_id + 1 # queue's addresses should be dumped by core id order
            csr_dump = re.findall(dump_regexp, line)
            if not csr_dump:
                queue_name = re.findall(queue_regexp, line)
                core_id = 0
                if queue_name:
                    parser_state = 1
                else:
                    parser_state = 0
        # default
        else:
            raise Exception("Parser state value not recognized")

    # Elaborate parsed data
    #TODO: change function basing on the systolic topology to analyze
    map_elab = systolic_map_conv2d(map_raw)

    # Dataframe
    df = pd.DataFrame(map_elab)
    df.set_index(['xqueue', 'core_id'], inplace=True)
    print(df)
    df.to_csv(OUTPUT_CSV)

if __name__ == '__main__':
    sys.exit(main())
