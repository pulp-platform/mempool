# Copyright 2025 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#

import sys

# Values for hex conversion
h2v = {'0': 0, '1': 1, '2': 2, '3': 3,
       '4': 4, '5': 5, '6': 6, '7': 7,
       '8': 8, '9': 9, 'A': 10, 'B': 11,
       'C': 12, 'D': 13, 'E': 14, 'F': 15}
v2h = {v: k for k, v in h2v.items()}

def hex2int(h):
    """Convert a hexadecimal string to an integer, always big-endian"""
    return sum(h2v[c] * (16 ** i) for i, c in enumerate(reversed(h)))

def int2hex(i):
    """Convert a long integer to hexadecimal string, always big-endian, 8 digits"""
    h = ''
    for n in range(8):
        e = 16 ** (7 - n)
        if e > i:
            h += '0'
        else:
            d = i // e
            h += v2h[d]
            i -= d * (16 ** (7 - n))
    return h

def swap_endian(d):
    """Swap endian: reverse the byte order in a hexadecimal string"""
    return ''.join(reversed([d[i:i+2] for i in range(0, len(d), 2)]))

def main():
    m = {}   # Memory hash (for 8-bit entries)
    m32 = {} # Memory hash (for 32-bit entries)
    prev_addr = 0

    # Read from stdin
    for line in sys.stdin:
        line = line.strip()
        if not line or not line.startswith("S3"):  # Skip empty lines or non-S3 lines
            continue

        line = line[4:].rstrip()  # Remove the first 4 chars and trailing whitespace

        addr = line[:8]            # Address is the first 8 characters
        aint = hex2int(addr)       # Address as an integer
        data = line[8:10]          # Data is the next 2 characters

        m[aint] = data             # Store in memory hash

    # Convert 8-bit entries to 32-bit entries
    for aint in sorted(m.keys()):
        data = m[aint]

        addr = (aint // 4) * 4    # Align address to 4-byte boundary

        if (addr - prev_addr > 4) and (addr % 8 != 0):  # Insert padding if needed
            m32[addr - 4] = "00000000"

        prev = "00000000"
        if addr in m32:
            prev = m32[addr]

        byte0, byte1, byte2, byte3 = prev[0:2], prev[2:4], prev[4:6], prev[6:8]

        # Switch case to place data in the right position
        if aint % 4 == 0:
            prev = f"{data}{byte1}{byte2}{byte3}"
        elif aint % 4 == 1:
            prev = f"{byte0}{data}{byte2}{byte3}"
        elif aint % 4 == 2:
            prev = f"{byte0}{byte1}{data}{byte3}"
        elif aint % 4 == 3:
            prev = f"{byte0}{byte1}{byte2}{data}"

        m32[addr] = prev
        prev_addr = addr

    # Output the 32-bit values in the required format
    all_addresses = sorted(m32.keys())
    i = 0

    while i <= len(all_addresses) - 1:
        a = all_addresses[i]
        if a % 8 == 4:
            a -= 4
            i += 1
        else:
            i += 2

        h = int2hex(a)
        lo, hi = "00000000", "00000000"
        miss = 0

        if a in m32:
            lo = swap_endian(m32[a])
        else:
            miss += 1

        if a + 4 in m32:
            hi = swap_endian(m32[a + 4])
        else:
            miss += 1

        if miss <= 1:
            print(f"{h}_{hi}{lo}")

if __name__ == "__main__":
    main()
