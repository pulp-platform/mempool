#!/usr/bin/env python3

# Copyright 2026 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Analyze benchmark stall data and generate overview and tile-detail plots.

The run's topology.env and stall CSV determine the available tiles and their
group/subgroup output directories. Each tile-detail plot shows its cores'
execution states and stall causes over time. Normal users should invoke
`make plots`; this script is its direct implementation.
"""

import argparse
import csv
import multiprocessing
import sys
from pathlib import Path

_root = str(Path(__file__).resolve().parent.parent)
if _root not in sys.path:
    sys.path.insert(0, _root)

from _workflow_metadata import describe, load_topology  # noqa: E402
import _stall_plots as stall_plots  # noqa: E402

# ---------------------------------------------------------------------------
# Topology and Data Preparation
# ---------------------------------------------------------------------------


def tile_output_dir(plots_dir, topo, tile_id):
    """Compute the output directory for a given tile ID."""
    group = tile_id // topo["tiles_per_group"]
    if topo["n_subgroups_per_group"] > 1:
        subgroup = ((tile_id % topo["tiles_per_group"])
                    // topo["tiles_per_subgroup"])
        return plots_dir / f"group{group}" / f"subgroup{subgroup}"
    return plots_dir / f"group{group}"


def discover_tile_ids(csv_path):
    """Read unique tile IDs from the CSV."""
    tiles = set()
    with csv_path.open(newline="") as f:
        for row in csv.DictReader(f):
            val = row.get("tile", "").strip()
            if val:
                tiles.add(int(val))
    return sorted(tiles)


def group_rows_by_tile(rows):
    grouped = {}
    for row in rows:
        tile_id = row.get("tile")
        if tile_id is None:
            continue
        grouped.setdefault(tile_id, []).append(row)
    return grouped


def validate_tiles(topo, tile_ids):
    if not tile_ids:
        raise ValueError('No tile IDs found in CSV')
    n_tiles = topo['n_tiles']
    invalid = [tile_id for tile_id in tile_ids
               if tile_id < 0 or tile_id >= n_tiles]
    if invalid:
        raise ValueError(
            f'Tiles {invalid[:5]} do not fit the topology '
            f'(expected tile IDs in [0, {n_tiles - 1}])')


def _filter_description(sections):
    if not sections:
        return "all rows"
    values = ",".join(str(value) for value in sorted(set(sections)))
    return f"section={values}"


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def parse_args(argv=None):
    p = argparse.ArgumentParser(
        description="Analyze stall data and generate overview and tile-detail "
                    "plots. A tile-detail plot shows per-core execution state "
                    "and stall causes for one tile.")
    p.add_argument(
        "result_dir",
        help="Benchmark result directory "
             "(e.g. results/matmul_i32_mempool/das)")
    p.add_argument("--section", type=int, action="append",
                   help="Filter by section (repeatable)")
    p.add_argument(
        "--overview",
        action="store_true",
        help="Also generate cluster overview and per-group breakdown pages")
    p.add_argument("--skip-tile-details", action="store_true",
                   help="Skip per-tile detail pages")
    p.add_argument("--window", type=int, default=64,
                   help="Time-series bin width in cycles (default: 64)")
    p.add_argument("--jobs", "-j", type=int, default=1,
                   help="Number of parallel tile-plot workers (default: 1)")
    p.add_argument("--dry-run", action="store_true",
                   help="Print what would be done without executing")
    args = p.parse_args(argv)
    if args.window <= 0:
        p.error("--window must be positive")
    if args.jobs <= 0:
        p.error("--jobs must be positive")
    return args


# ---------------------------------------------------------------------------
# Tile Plot Generation
# ---------------------------------------------------------------------------

def _render_tile(item):
    """Render one tile page and return its tile ID and any error."""
    tid, out_dir, tile_rows = item
    try:
        if not tile_rows:
            raise ValueError(f"No rows for tile {tid}")
        out_dir.mkdir(parents=True, exist_ok=True)
        ts = stall_plots.build_tile_series(tile_rows, tid)
        stall_plots.write_tile_detail(
            out_dir / f"tile_detail_tile{tid}.png", ts)
        return (tid, None)
    except Exception as e:
        return (tid, str(e))


# ---------------------------------------------------------------------------
# Workflow
# ---------------------------------------------------------------------------

def main(argv=None):
    args = parse_args(argv)
    result_dir = Path(args.result_dir).resolve()

    # Resolve the run inputs and topology.
    csv_path = result_dir / "data" / "stall_timeseries_benchmark.csv"
    plots_dir = result_dir / "plots"

    if not csv_path.is_file():
        sys.exit(f"CSV not found: {csv_path}")

    try:
        topo = load_topology(result_dir / "topology.env")
    except ValueError as exc:
        sys.exit(str(exc))

    print(f"Topology: {describe(topo)}")
    print(f"CSV:      {csv_path}")
    print(f"Plots:    {plots_dir}")

    # Load rows when rendering needs them; otherwise discover only tile IDs.
    rows = None
    needs_rows = not args.dry_run and (
        args.overview or not args.skip_tile_details)
    if needs_rows:
        print("Loading stall CSV ...", flush=True)
        rows = stall_plots.filter_rows(
            stall_plots.load_rows(csv_path), section=args.section)
        if not rows:
            sys.exit("No rows after filtering")
        tile_ids = sorted({row["tile"] for row in rows
                           if row.get("tile") is not None})
    else:
        tile_ids = discover_tile_ids(csv_path)

    try:
        validate_tiles(topo, tile_ids)
    except ValueError as exc:
        sys.exit(str(exc))

    print(f"Tiles:    {len(tile_ids)} ({tile_ids[0]}–{tile_ids[-1]})")
    print()

    # Prepare the requested overview and tile-detail outputs.
    overview_dir = plots_dir / "overview"
    digits = len(str(max(topo["n_tiles"] - 1, 1)))

    work_items = []
    if args.skip_tile_details:
        print("Tile details: skipped (--skip-tile-details)")
    else:
        for tid in tile_ids:
            out_dir = tile_output_dir(plots_dir, topo, tid)
            work_items.append((tid, out_dir))

    if args.dry_run:
        if args.overview:
            print(f"[dry-run] overview → {overview_dir}")
        for tid, out_dir in work_items:
            label = (
                f"tile {tid:0{digits}d} → "
                f"{out_dir.relative_to(plots_dir)}")
            print(f"[dry-run] {label}")
        return

    rows_by_tile = group_rows_by_tile(rows) if work_items else {}
    failed = []

    if args.overview:
        overview_dir.mkdir(parents=True, exist_ok=True)
        filter_desc = _filter_description(args.section)

        print(f"Overview → {overview_dir}")
        agg = stall_plots.aggregate_rows(
            rows, args.window, context_field="tile")
        stall_plots.write_overview_page(
            overview_dir / "overview_workload.png",
            agg, filter_desc, args.window)
        group_stats = stall_plots.build_group_overview_stats(rows)
        stall_plots.write_group_overview_page(
            overview_dir / "group_ipc_breakdown.png",
            group_stats, filter_desc)
        print()

    if work_items:
        n_jobs = min(args.jobs, len(work_items))

        if n_jobs <= 1:
            for i, (tid, out_dir) in enumerate(work_items, 1):
                label = (f"[{i}/{len(work_items)}] tile {tid:0{digits}d} "
                         f"→ {out_dir.relative_to(plots_dir)}")
                print(label, end=" ... ", flush=True)
                _, error = _render_tile(
                    (tid, out_dir, rows_by_tile.get(tid)))
                if error is None:
                    print("ok")
                else:
                    print(f"FAILED: {error}")
                    failed.append((tid, error))
        else:
            print(
                f"Generating {len(work_items)} tile plots "
                f"with {n_jobs} parallel workers ...")
            # Use spawn context to avoid fork-safety issues with matplotlib.
            # Each worker receives its tile's already-parsed rows, so the
            # CSV is only read once, in this process.
            ctx = multiprocessing.get_context("spawn")
            payloads = [(tid, out_dir, rows_by_tile.get(tid))
                        for tid, out_dir in work_items]
            with ctx.Pool(n_jobs) as pool:
                results = pool.map(_render_tile, payloads)
            for tid, err in results:
                if err is not None:
                    failed.append((tid, err))
            print(f"  {len(work_items) - len(failed)} ok, "
                  f"{len(failed)} failed")

    # Report generated outputs and any per-tile failures.
    parts = []
    if args.skip_tile_details:
        parts.append("tile details skipped")
    else:
        generated = len(work_items) - len(failed)
        parts.append(f"{generated} tile details generated")
    if args.overview:
        parts.append("overview generated")
    if failed:
        parts.append(f"{len(failed)} failed")
    print(f"\nDone: {' / '.join(parts)}  ({len(tile_ids)} total)")
    if failed:
        print("Failed tiles:")
        for tid, err in failed:
            print(f"  tile {tid}: {err}")
        sys.exit(1)


if __name__ == "__main__":
    main()
