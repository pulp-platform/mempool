#!/usr/bin/env python3

# Copyright 2026 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Merge a testbench TCDM address trace into a raw core trace."""

import argparse
import csv
import re
import sys
from pathlib import Path


# Raw trace:
#   <time> <cycle> <pc> <instruction> #; {
#     'source': 0x00000000,
#     'stall': 0x0,
#     ...
#     'is_load': 0x1,
#     'is_store': 0x0,
#     ...
#   }
# Accepted requests have 'stall': 0x0 and either 'is_load' or 'is_store'
# set to 0x1. Other signal values are not used here.
# Extra TCDM address trace, generated when address tracing is enabled:
#   <cycle>,<tcdm_addr>  (no header row)
# Accepted requests are joined on <cycle>, then 'tcdm_addr' is added to the
# raw trace signal values.
_CYCLE_RE = re.compile(r"^\s*\d+\s+(\d+)\s+")


def _load_addresses(path):
    addresses = {}
    with path.open(newline="") as infile:
        for line_no, row in enumerate(csv.reader(infile), 1):
            if len(row) != 2:
                raise ValueError(f"Malformed address trace {path}:{line_no}")
            cycle, address = int(row[0], 0), int(row[1], 0)
            # A core can accept at most one LSU request per cycle.
            if cycle in addresses:
                raise ValueError(f"Duplicate cycle in {path}:{line_no}")
            addresses[cycle] = address
    return addresses


def _issue_cycle(line):
    if ("'stall': 0x0" not in line or
            ("'is_load': 0x1" not in line and
             "'is_store': 0x1" not in line)):
        return None
    match = _CYCLE_RE.match(line)
    return int(match.group(1)) if match else None


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("trace", type=argparse.FileType("r"))
    parser.add_argument("addresses", type=Path)
    args = parser.parse_args(argv)

    if not args.addresses.is_file():
        raise SystemExit(
            f"Missing TCDM address trace: {args.addresses}")

    addresses = _load_addresses(args.addresses)
    # Check the core trace and TCDM address trace before writing output.
    issue_cycles = {
        cycle for line in args.trace
        if (cycle := _issue_cycle(line)) is not None
    }
    missing = issue_cycles - addresses.keys()
    unused = addresses.keys() - issue_cycles
    if missing or unused:
        raise SystemExit(
            f"TCDM address mismatch for {args.addresses}: "
            f"{len(missing)} missing, {len(unused)} unused\n"
            "The core and TCDM address traces must come from the same "
            "simulation.")

    # Rewind after validation so an error cannot leave partial output.
    args.trace.seek(0)
    for line in args.trace:
        cycle = _issue_cycle(line)
        address = addresses.get(cycle) if cycle is not None else None
        body = line.rstrip()
        if (address is not None and "'tcdm_addr'" not in body and
                "#;" in body and body.endswith("}")):
            prefix = body[:-1].rstrip(", ")
            line = f"{prefix}, 'tcdm_addr': 0x{address:08x}}}\n"
        sys.stdout.write(line)
    return 0


if __name__ == "__main__":
    sys.exit(main())
