#!/usr/bin/env python3

# Copyright 2026 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Merge per-trace performance CSV fragments into one results.csv.

During `make trace`, every hart writes its own small CSV fragment so that
parallel trace generation never appends to a shared file. This script merges
the fragments into a single results.csv, sorted by core and section.
"""

from __future__ import annotations

import argparse
import csv
import sys
from pathlib import Path

# Performance rows contain list-valued fields that can exceed the CSV default.
csv.field_size_limit(sys.maxsize)


def parse_args(argv=None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description='Merge per-trace performance CSV fragments '
                    'into one results.csv.')
    parser.add_argument(
        '--folder',
        required=True,
        help='Directory containing per-trace CSV fragments.',
    )
    parser.add_argument(
        '--csv',
        required=True,
        help='Merged CSV output path.',
    )
    parser.add_argument(
        '--expected-count',
        type=int,
        help='Expected number of fragment CSV files. If set, refuse to '
             'merge when the count differs.',
    )
    return parser.parse_args(argv)


def load_fragment(fragment_path: Path) -> tuple[list[str], list[list[str]]]:
    with fragment_path.open(newline='') as handle:
        reader = csv.reader(handle)
        try:
            header = next(reader)
        except StopIteration:
            return [], []
        rows = [row for row in reader if any(value != '' for value in row)]
    return header, rows


def main(argv=None) -> int:
    args = parse_args(argv)
    fragment_dir = Path(args.folder)
    output_path = Path(args.csv)

    fragment_paths = sorted(fragment_dir.glob('*.csv'))
    if not fragment_paths:
        sys.stderr.write(f'ERROR: no CSV fragments found in {fragment_dir}\n')
        return 1
    if args.expected_count is not None and len(
            fragment_paths) != args.expected_count:
        sys.stderr.write(
            f'ERROR: expected {args.expected_count} CSV fragments in '
            f'{fragment_dir}, but found {len(fragment_paths)}\n')
        return 1

    merged_header: list[str] | None = None
    merged_rows: list[list[str]] = []
    fragment_count = 0

    for fragment_path in fragment_paths:
        header, rows = load_fragment(fragment_path)
        if not header:
            continue
        if merged_header is None:
            merged_header = header
        elif header != merged_header:
            sys.stderr.write(
                f'ERROR: header mismatch in {fragment_path}; expected '
                f'exact match to first fragment\n')
            return 1
        fragment_count += 1
        merged_rows.extend(rows)

    if merged_header is None or not merged_rows:
        sys.stderr.write(
            f'ERROR: no performance rows found in {fragment_dir}\n')
        return 1

    try:
        core_index, section_index = (
            merged_header.index(column) for column in ('core', 'section'))
        merged_rows.sort(
            key=lambda row: (int(row[core_index]), int(row[section_index])))
    except (IndexError, ValueError) as error:
        sys.stderr.write(f'ERROR: invalid core or section column: {error}\n')
        return 1

    output_path.parent.mkdir(parents=True, exist_ok=True)
    with output_path.open('w', newline='') as handle:
        writer = csv.writer(handle)
        writer.writerow(merged_header)
        writer.writerows(merged_rows)

    print(f'Merged {len(merged_rows)} rows from {fragment_count} '
          f'fragment files into {output_path}')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
