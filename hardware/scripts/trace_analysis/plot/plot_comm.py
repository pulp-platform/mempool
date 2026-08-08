#!/usr/bin/env python3

# Copyright 2026 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Analyze benchmark communication data and generate traffic and latency plots.

Usage:
    python plot_comm.py <result_dir> [--section 1] [--window 64]
"""

from __future__ import annotations

import argparse
import csv
import math
import sys
from collections import defaultdict
from pathlib import Path

_root = str(Path(__file__).resolve().parent.parent)
if _root not in sys.path:
    sys.path.insert(0, _root)

from _workflow_metadata import load_topology  # noqa: E402

import matplotlib  # noqa: E402
matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402
import matplotlib.gridspec as gridspec  # noqa: E402
from matplotlib.patches import Rectangle  # noqa: E402
from matplotlib.colors import (  # noqa: E402
    LinearSegmentedColormap,
    LogNorm,
    Normalize,
    PowerNorm,
)
from mpl_toolkits.axes_grid1 import make_axes_locatable  # noqa: E402
import numpy as np  # noqa: E402

# ---------------------------------------------------------------------------
# Plot Style
# ---------------------------------------------------------------------------

FONT_SUBTITLE = 11
FONT_LABEL = 10.5
FONT_TICK = 9
FONT_ANNOT = 8.5
FONT_LEGEND = 9

# Colorblind-safe palette (Okabe-Ito-inspired)
COL_LOCAL = "#0072B2"   # blue  – local / intra-tile
COL_SAME_SUB = "#009E73"  # green – same subgroup, different tile
COL_SAME_GRP = "#56B4E9"  # sky blue – same group, different tile
COL_REMOTE = "#D55E00"  # vermillion – remote / inter-group
COL_ACCENT = "#E69F00"  # amber – highlights / p95
COL_NEUTRAL = "#999999"

GRP_COLORS = ["#0072B2", "#E69F00", "#009E73", "#CC79A7"]
LATENCY_CMAP_COLORS = (
    "#1a9641", "#55b748", "#91cf60", "#d0ec8a", "#f0f4a4",
    "#fee08b", "#fdae61", "#f46d43", "#d73027", "#a50026",
)

DPI = 300
FIG_TEXT_COLOR = "#222222"
MATRIX_ANNOTATION_LIMIT = 64

LOCALITY_LABELS = {
    "local": "Same tile",
    "same_subgroup": "Same subgroup",
    "same_group": "Same group",
    "remote": "Other group",
}


def _apply_style():
    """Configure matplotlib for publication-quality output."""
    plt.rcParams.update({
        "font.family": "serif",
        "font.size": FONT_TICK,
        "axes.titlesize": FONT_SUBTITLE,
        "axes.labelsize": FONT_LABEL,
        "axes.edgecolor": "#444444",
        "axes.linewidth": 0.7,
        "axes.facecolor": "white",
        "figure.facecolor": "white",
        "xtick.labelsize": FONT_TICK,
        "ytick.labelsize": FONT_TICK,
        "xtick.direction": "out",
        "ytick.direction": "out",
        "xtick.major.size": 3.5,
        "ytick.major.size": 3.5,
        "xtick.minor.size": 2.0,
        "ytick.minor.size": 2.0,
        "legend.fontsize": FONT_LEGEND,
        "legend.frameon": True,
        "legend.framealpha": 0.92,
        "legend.edgecolor": "#cccccc",
        "legend.fancybox": True,
        "grid.alpha": 0.25,
        "grid.color": "#888888",
        "grid.linewidth": 0.5,
        "savefig.bbox": "tight",
        "savefig.pad_inches": 0.08,
        "text.color": FIG_TEXT_COLOR,
        "axes.labelcolor": FIG_TEXT_COLOR,
    })


# ---------------------------------------------------------------------------
# Data Loading
# ---------------------------------------------------------------------------

def _int(value):
    return None if value is None or value == "" else int(value)


def _iter_events(path: Path, section):
    """Yield selected CSV rows without retaining the event file."""
    with path.open(newline="") as f:
        for row in csv.DictReader(f):
            if section is None or _int(row.get("section")) == section:
                yield row


# ---------------------------------------------------------------------------
# Communication Aggregation
# ---------------------------------------------------------------------------

def _classify_locality(row):
    """Return the most specific source-to-destination locality class."""
    if _int(row.get("is_local")) == 1:
        return "local"
    if _int(row.get("is_same_subgroup")) == 1:
        return "same_subgroup"
    if _int(row.get("is_same_group")) == 1:
        return "same_group"
    return "remote"


def _scan_events(events, topology):
    """Collect fixed-size aggregates and cycle bounds in one CSV pass."""
    n_groups = topology["n_groups"]
    n_tiles = topology["n_tiles"]
    tiles_per_group = topology["tiles_per_group"]
    tile_matrix = np.zeros((n_tiles, n_tiles), dtype=float)
    group_matrix = np.zeros((n_groups, n_groups), dtype=float)
    pair_data = defaultdict(
        lambda: {"count": 0, "lat_sum": 0.0, "locality": "remote"})

    event_count = 0
    min_cycle = None
    max_cycle = None
    has_traffic = False

    for row in events:
        event_count += 1
        cycle_s = row.get("cycle")
        if cycle_s not in (None, ""):
            cycle = int(cycle_s)
            min_cycle = cycle if min_cycle is None else min(
                min_cycle, cycle)
            max_cycle = cycle if max_cycle is None else max(
                max_cycle, cycle)

        event_type = (row.get("event_type") or "").strip()
        if event_type in ("load_issue", "store_issue"):
            dest_s = (row.get("dest_tile") or "").strip()
            source = _int(row.get("tile"))
            if dest_s:
                dest = int(dest_s)
                if (source is not None and 0 <= source < n_tiles and
                        0 <= dest < n_tiles):
                    has_traffic = True
                    tile_matrix[source, dest] += 1
                    group_matrix[
                        source // tiles_per_group,
                        dest // tiles_per_group,
                    ] += 1

        if event_type == "load_return":
            source = _int(row.get("tile"))
            dest_s = (row.get("dest_tile") or "").strip()
            latency_s = row.get("latency", "")
            if source is not None and dest_s and latency_s:
                pair = pair_data[(source, int(dest_s))]
                pair["count"] += 1
                pair["lat_sum"] += float(latency_s)
                pair["locality"] = _classify_locality(row)

    cycle_bounds = ((min_cycle, max_cycle)
                    if min_cycle is not None else None)
    matrices = None
    if has_traffic:
        matrices = {"mat": tile_matrix, "gmat": group_matrix}
    return {
        "event_count": event_count,
        "cycle_bounds": cycle_bounds,
        "matrices": matrices,
        "pair_data": pair_data,
    }


def _build_timeseries(events, topology, window_size, cycle_bounds):
    """Bin issued requests and load-return latency into cycle windows."""
    if window_size <= 0:
        raise ValueError("window size must be positive")
    if cycle_bounds is None:
        return None
    min_cycle, max_cycle = cycle_bounds
    n_windows = (max_cycle - min_cycle) // window_size + 1
    n_groups = topology["n_groups"]
    n_tiles = topology["n_tiles"]
    tiles_per_group = topology["tiles_per_group"]
    localities = tuple(LOCALITY_LABELS)

    requests = {name: np.zeros(n_windows) for name in localities}
    incoming = np.zeros((n_tiles, n_windows))
    latency_total = np.zeros((n_tiles, n_windows))
    latency_count = np.zeros((n_tiles, n_windows), dtype=int)
    locality_total = {
        name: np.zeros((n_tiles, n_windows)) for name in localities}
    locality_count = {
        name: np.zeros((n_tiles, n_windows), dtype=int)
        for name in localities
    }
    for r in events:
        cyc_s = r.get("cycle", "")
        tile_s = r.get("tile", "")
        if not cyc_s or not tile_s:
            continue
        tile = int(tile_s)
        column = (int(cyc_s) - min_cycle) // window_size
        valid_tile = 0 <= tile < n_tiles

        et = (r.get("event_type") or "").strip()
        is_request = et in ("load_issue", "store_issue")
        dest_s = (r.get("dest_tile") or "").strip()
        # A request without a decoded destination has no known locality.
        if is_request and valid_tile and dest_s:
            locality = _classify_locality(r)
            requests[locality][column] += 1

        lat_s = r.get("latency", "")
        if valid_tile and lat_s and et == "load_return":
            lat = float(lat_s)
            latency_total[tile, column] += lat
            latency_count[tile, column] += 1
            locality = _classify_locality(r)
            locality_total[locality][tile, column] += lat
            locality_count[locality][tile, column] += 1

        if is_request and dest_s:
            dest = int(dest_s)
            if 0 <= dest < n_tiles:
                incoming[dest, column] += 1

    tile_latency = np.divide(
        latency_total, latency_count,
        out=np.full((n_tiles, n_windows), np.nan),
        where=latency_count > 0)
    system_total = latency_total.sum(axis=0)
    system_count = latency_count.sum(axis=0)
    group_shape = (n_groups, tiles_per_group, n_windows)
    group_total = latency_total.reshape(group_shape).sum(axis=1)
    group_count = latency_count.reshape(group_shape).sum(axis=1)
    class_total = {
        name: values.sum(axis=0)
        for name, values in locality_total.items()
    }
    class_count = {
        name: values.sum(axis=0)
        for name, values in locality_count.items()
    }

    def averages(total, count):
        return np.divide(total, count, out=np.full(total.shape, np.nan),
                         where=count > 0)

    cycle_centers = (
        min_cycle + np.arange(n_windows) * window_size + window_size / 2.0)
    group_cycles = np.tile(cycle_centers, (n_groups, 1))

    return {
        "cycles": cycle_centers,
        "group_cycles": group_cycles,
        "cycle_bounds": (
            min_cycle,
            min_cycle + n_windows * window_size - 1,
        ),
        "window_size": window_size,
        "n_windows": n_windows,
        "n_groups": n_groups,
        "n_tiles": n_tiles,
        "tiles_per_group": tiles_per_group,
        "n_subgroups_per_group": topology["n_subgroups_per_group"],
        "requests": requests,
        "incoming": incoming,
        "latency": {
            "system": averages(system_total, system_count),
            "group": averages(group_total, group_count),
            "tile": tile_latency,
            "locality": {
                name: averages(class_total[name], class_count[name])
                for name in localities
            },
        },
    }


# ---------------------------------------------------------------------------
# Shared Figure Helpers
# ---------------------------------------------------------------------------

def _nice_count(value):
    """Format a count for plot annotations (e.g., 1234 → '1.2k')."""
    if value >= 1_000_000:
        return f"{value / 1_000_000:.1f}M"
    if value >= 1000:
        return f"{value / 1000:.1f}k"
    return f"{value:.0f}"


def _add_subgroup_boxes(
        ax, topology, tiles_per_group, n_groups, zorder_base=7):
    """Draw subgroup boxes, boundaries, and labels on a tile matrix."""
    tiles_per_subgroup = topology.get("tiles_per_subgroup")
    n_subgroups = topology.get("n_subgroups_per_group")
    n_tiles = n_groups * tiles_per_group
    if (not tiles_per_subgroup or not n_subgroups or
            tiles_per_subgroup >= tiles_per_group):
        return

    # Mark subgroup boundaries without redrawing group boundaries.
    for boundary in range(tiles_per_subgroup, n_tiles, tiles_per_subgroup):
        if boundary % tiles_per_group != 0:
            ax.axhline(boundary - 0.5, color="#888888", lw=0.6,
                       ls="--", alpha=0.5, zorder=3)
            ax.axvline(boundary - 0.5, color="#888888", lw=0.6,
                       ls="--", alpha=0.5, zorder=3)

    # Outline same-subgroup blocks on the matrix diagonal.
    for group in range(n_groups):
        color = GRP_COLORS[group % len(GRP_COLORS)]
        for subgroup in range(n_subgroups):
            origin = (group * tiles_per_group +
                      subgroup * tiles_per_subgroup - 0.5)
            ax.add_patch(Rectangle(
                (origin, origin), tiles_per_subgroup, tiles_per_subgroup,
                linewidth=1.5, edgecolor=color,
                facecolor="none", ls="--", alpha=0.7,
                zorder=zorder_base, clip_on=False,
            ))

    # Label each subgroup between the group labels and tile tick labels.
    for group in range(n_groups):
        color = GRP_COLORS[group % len(GRP_COLORS)]
        for subgroup in range(n_subgroups):
            midpoint = (group * tiles_per_group +
                        subgroup * tiles_per_subgroup +
                        tiles_per_subgroup / 2)
            ax.text(-0.02, midpoint, f"s{subgroup}",
                    ha="right", va="center",
                    fontsize=FONT_ANNOT - 1, color=color, alpha=0.6,
                    transform=ax.get_yaxis_transform(), clip_on=False)
            ax.text(midpoint, -0.03, f"s{subgroup}",
                    ha="center", va="top",
                    fontsize=FONT_ANNOT - 1, color=color, alpha=0.6,
                    transform=ax.get_xaxis_transform(), clip_on=False)


def _clean_spine(ax, top=False, right=False):
    """Remove top/right spines and enable y-grid."""
    ax.spines["top"].set_visible(top)
    ax.spines["right"].set_visible(right)
    ax.grid(axis="y", alpha=0.25)
    ax.set_axisbelow(True)


def _save(fig, output_dir, name, dpi=DPI):
    output_dir.mkdir(parents=True, exist_ok=True)
    fig.savefig(output_dir / f"{name}.png", dpi=dpi)
    plt.close(fig)
    print(f"  → {name}.png")


def _matrix_pixel_budget(n_tiles):
    return 8000 if n_tiles > MATRIX_ANNOTATION_LIMIT else 5400


# ---------------------------------------------------------------------------
# Group-to-Group Request Matrix
# ---------------------------------------------------------------------------

def plot_traffic_matrix_group(matrices, topology, output_dir, section):
    """Plot issued request counts by source and destination group."""
    n_groups = topology["n_groups"]
    if matrices is None:
        print("  [skip] No traffic data for matrix")
        return

    gmat = matrices["gmat"]
    sec_lbl = f"Section {section}" if section is not None else "All sections"

    fig, ax = plt.subplots(figsize=(7.2, 5.8))
    gmax = gmat.max()
    image = ax.imshow(
        gmat,
        origin="lower",
        cmap="YlOrRd",
        aspect="equal",
        norm=Normalize(
            vmin=0,
            vmax=gmax),
        interpolation="nearest")
    for i in range(n_groups):
        for j in range(n_groups):
            val = gmat[i, j]
            txt_col = "white" if val > gmax * 0.6 else FIG_TEXT_COLOR
            if val > 0:
                ax.text(
                    j,
                    i,
                    _nice_count(val),
                    ha="center",
                    va="center",
                    fontsize=FONT_ANNOT + 1,
                    fontweight="bold",
                    color=txt_col)
    ax.set_xticks(range(n_groups))
    ax.set_yticks(range(n_groups))
    ax.set_xticklabels(
        [f"Group {g}" for g in range(n_groups)], fontsize=FONT_TICK)
    ax.set_yticklabels(
        [f"Group {g}" for g in range(n_groups)], fontsize=FONT_TICK)
    ax.set_xlabel("Destination group", fontsize=FONT_LABEL)
    ax.set_ylabel("Source group", fontsize=FONT_LABEL)
    ax.set_title("Group-to-group request volume (load/store issues)",
                 fontsize=FONT_SUBTITLE, fontweight="bold", pad=10)
    divider = make_axes_locatable(ax)
    colorbar_ax = divider.append_axes("right", size="3.5%", pad=1.00)
    colorbar = fig.colorbar(image, cax=colorbar_ax)
    colorbar.set_label("Load/store issues", fontsize=FONT_LABEL - 1)
    colorbar.ax.tick_params(labelsize=FONT_TICK - 1)

    total = gmat.sum()
    group_nonzero = int(np.count_nonzero(gmat))
    fig.text(
        0.5, -0.02,
        f"{sec_lbl}  ·  {n_groups} groups  ·  "
        f"{_nice_count(total)} requests  ·  "
        f"{group_nonzero} active group pairs", ha="center",
        fontsize=FONT_ANNOT, color="#666666", style="italic")

    _save(fig, output_dir, "traffic_matrix_groups")


# ---------------------------------------------------------------------------
# Tile-to-Tile Request Matrix
# ---------------------------------------------------------------------------

def plot_traffic_matrix_full(matrices, topology, output_dir, section):
    """Full-chip square tile-to-tile request heatmap (n_tiles × n_tiles).
    All groups are shown on both axes so the matrix is always square."""
    n_groups = topology["n_groups"]
    if matrices is None:
        print("  [skip] No traffic data for tile matrix")
        return

    mat = matrices["mat"]
    n_tiles = topology["n_tiles"]
    tiles_per_group = topology["tiles_per_group"]

    # Scale matrix cells to keep annotations readable.
    max_px = _matrix_pixel_budget(n_tiles)
    cell_size = max(0.20, min(0.50, (max_px / DPI - 2.5) / max(n_tiles, 1)))
    side_inches = max(6.0, n_tiles * cell_size)
    fig_w = side_inches + 2.5  # colorbar + labels
    fig_h = side_inches + 2.0  # title + xlabel
    fig, ax = plt.subplots(figsize=(fig_w, fig_h))

    vmax = mat.max()
    plot_matrix = mat.copy()
    vmin = max(1.0, mat[mat > 0].min()) if np.any(mat > 0) else 1.0
    plot_matrix[plot_matrix == 0] = np.nan
    cmap = plt.cm.YlOrRd.copy()
    cmap.set_bad(color="#F5F5F5")
    im = ax.imshow(plot_matrix, origin="lower", cmap=cmap, aspect="equal",
                   norm=LogNorm(vmin=vmin, vmax=vmax), interpolation="nearest")

    # Annotate cells — font scales with cell size for readability.
    if n_tiles <= MATRIX_ANNOTATION_LIMIT:
        cell_pt = cell_size * 72
        annot_fs = min(FONT_ANNOT, max(2.0, cell_pt * 0.28))
        fw = "bold" if n_tiles <= 32 else "normal"
        for i in range(n_tiles):
            for j in range(n_tiles):
                val = mat[i, j]
                if val > 0:
                    txt_col = (
                        "white" if val > vmax * 0.3 else FIG_TEXT_COLOR)
                    ax.text(j, i, _nice_count(val), ha="center", va="center",
                            fontsize=annot_fs, fontweight=fw, color=txt_col)

    # Group boundaries — source (y-axis)
    for g in range(n_groups):
        offset = g * tiles_per_group
        if g > 0:
            ax.axhline(offset - 0.5, color="#333333", lw=2.0, alpha=0.7)
        mid = offset + tiles_per_group / 2
        ax.text(-0.04, mid, f"G{g}", ha="right", va="center",
                fontsize=FONT_ANNOT + 3, fontweight="bold",
                color=GRP_COLORS[g % len(GRP_COLORS)],
                transform=ax.get_yaxis_transform(), clip_on=False)

    # Group boundaries — dest (x-axis)
    for g in range(n_groups):
        offset = g * tiles_per_group
        if g > 0:
            ax.axvline(offset - 0.5, color="#333333", lw=2.0, alpha=0.7)
        mid = offset + tiles_per_group / 2
        ax.text(mid, -0.06, f"G{g}", ha="center", va="top",
                fontsize=FONT_ANNOT + 3, fontweight="bold",
                color=GRP_COLORS[g % len(GRP_COLORS)],
                transform=ax.get_xaxis_transform(), clip_on=False)

    # Highlight self-group diagonal blocks
    for g in range(n_groups):
        origin = g * tiles_per_group - 0.5
        rect_xy = (origin, origin)
        gcol = GRP_COLORS[g % len(GRP_COLORS)]
        ax.add_patch(Rectangle(
            rect_xy, tiles_per_group, tiles_per_group,
            linewidth=4.0, edgecolor="#000000",
            facecolor="none", alpha=0.2, zorder=4, clip_on=False,
        ))
        ax.add_patch(Rectangle(
            rect_xy, tiles_per_group, tiles_per_group,
            linewidth=2.5, edgecolor=gcol,
            facecolor="none", zorder=5, clip_on=False,
        ))

    # Highlight self-subgroup diagonal blocks
    _add_subgroup_boxes(ax, topology, tiles_per_group, n_groups)

    # Tick labels — show ticks at subgroup boundaries for readability
    if n_tiles > 64:
        _tps = topology.get("tiles_per_subgroup")
        if _tps:
            tick_positions = list(range(0, n_tiles, _tps))
            if (n_tiles - 1) not in tick_positions:
                tick_positions.append(n_tiles - 1)
        else:
            tick_positions = list(range(0, n_tiles, tiles_per_group))
            tick_positions.append(n_tiles - 1)
        tick_labels = [str(t) for t in tick_positions]
        ax.set_xticks(tick_positions)
        ax.set_yticks(tick_positions)
        ax.set_xticklabels(tick_labels, fontsize=FONT_TICK - 1, rotation=90)
        ax.set_yticklabels(tick_labels, fontsize=FONT_TICK - 1)
    else:
        tick_fs = max(6.5, FONT_TICK - 1.0 * (n_tiles > 48))
        ax.set_xticks(range(n_tiles))
        ax.set_yticks(range(n_tiles))
        ax.set_xticklabels(range(n_tiles), fontsize=tick_fs, rotation=90)
        ax.set_yticklabels(range(n_tiles), fontsize=tick_fs)
    ax.set_xlabel("Destination tile", fontsize=FONT_LABEL, labelpad=20)
    ax.set_ylabel("Source tile", fontsize=FONT_LABEL)

    ax.set_title("Tile-to-tile request volume (load/store issues)",
                 fontsize=FONT_SUBTITLE, fontweight="bold", pad=10)

    divider = make_axes_locatable(ax)
    cax = divider.append_axes("right", size="3.5%", pad=1.00)
    cb = fig.colorbar(im, cax=cax)
    cb.set_label("Load/store issues", fontsize=FONT_LABEL - 1)
    # Use 1, 2.5, and 5 ticks per decade.
    low, high = math.log10(max(vmin, 1)), math.log10(max(vmax, 1))
    ticks = []
    for exp in range(int(math.floor(low)), int(math.ceil(high)) + 1):
        base = 10 ** exp
        for mult in [1, 2.5, 5]:
            v = base * mult
            if vmin <= v <= vmax:
                ticks.append(v)
    if not ticks:
        ticks = [vmin, vmax]
    cb.set_ticks(ticks)
    cb.set_ticklabels([_nice_count(tick) for tick in ticks])
    cb.ax.tick_params(labelsize=FONT_TICK)

    total = mat.sum()
    nonzero = int(np.count_nonzero(mat))
    sec_lbl = f"Section {section}" if section is not None else "All sections"
    fig.text(0.5, -0.005,
             f"{sec_lbl}  ·  {n_tiles} tiles  ·  {n_groups} groups  ·  "
             f"{_nice_count(total)} requests  ·  {nonzero} active pairs",
             ha="center", fontsize=FONT_ANNOT, color="#666666", style="italic")

    _save(fig, output_dir, "traffic_matrix")


# ---------------------------------------------------------------------------
# Temporal Communication Profile
# ---------------------------------------------------------------------------

def plot_temporal_profile(
        timeseries,
        output_dir,
        section):
    """Plot three communication views over a shared cycle axis.

      (a) Issued requests by topology-aware locality class
      (b) Issued requests received by each physical destination tile
      (c) Load-return latency, overall and by locality class
    """
    cycle_centers = timeseries["cycles"]
    section_start_cycle, section_end_cycle = timeseries["cycle_bounds"]
    n_windows = timeseries["n_windows"]
    n_groups = timeseries["n_groups"]
    n_tiles = timeseries["n_tiles"]
    tiles_per_group = timeseries["tiles_per_group"]
    requests = timeseries["requests"]
    heatmap_in = timeseries["incoming"]
    latency = timeseries["latency"]
    rel_cycle_centers = cycle_centers - section_start_cycle
    has_subgroups = (timeseries["n_subgroups_per_group"] or 1) > 1
    display_localities = [
        ("local", COL_LOCAL, LOCALITY_LABELS["local"], "Same-tile Avg."),
    ]
    if has_subgroups:
        display_localities.extend([
            ("same_subgroup", COL_SAME_SUB,
             LOCALITY_LABELS["same_subgroup"], "Same-subgroup Avg."),
            ("same_group", COL_SAME_GRP,
             LOCALITY_LABELS["same_group"], "Same-group Avg."),
        ])
    else:
        display_localities.append(
            ("same_subgroup", COL_SAME_GRP, "Same group", "Same-group Avg."))
    display_localities.append(
        ("remote", COL_REMOTE, LOCALITY_LABELS["remote"],
         "Other-group Avg."))

    fig = plt.figure(figsize=(12.8, 10.8))
    gs_fig = gridspec.GridSpec(
        3, 2,
        width_ratios=[40, 1.5],
        height_ratios=[1.2, 1.5, 1.0],
        hspace=0.34,
        wspace=0.24,
    )
    x_min = 0
    x_max = section_end_cycle - section_start_cycle
    x_label = (f"Cycles (Section {section})"
               if section is not None else "Cycles")

    # (a) Issued requests stacked by locality class.
    ax_a = fig.add_subplot(gs_fig[0, 0])
    stack = np.zeros(n_windows)
    for key, color, label, _ in display_localities:
        next_stack = stack + requests[key]
        ax_a.fill_between(rel_cycle_centers, stack, next_stack,
                          step="mid", color=color,
                          alpha=0.85 if key == "local" else 0.75,
                          label=label)
        stack = next_stack
    ax_a.set_xlim(x_min, x_max)
    ax_a.set_ylabel("Issued requests / window", fontsize=FONT_LABEL)
    ax_a.set_title(
        "(a)  Issued memory requests by locality class",
        fontsize=FONT_SUBTITLE,
        fontweight="bold",
        pad=6,
        loc="left")
    ax_a.legend(loc="upper right", fontsize=FONT_LEGEND, ncol=2)
    _clean_spine(ax_a)
    ax_a.tick_params(labelbottom=True)
    ax_a.set_xlabel(x_label, fontsize=FONT_LABEL, labelpad=2)

    # (b) Issued requests grouped by their physical destination tile.
    ax_b = fig.add_subplot(gs_fig[1, 0], sharex=ax_a)
    extent = [0, x_max,
              -0.5, n_tiles - 0.5]
    vmax_heat = (np.percentile(heatmap_in[heatmap_in > 0], 95)
                 if np.any(heatmap_in > 0) else 1)
    cmap_heat = plt.cm.YlOrRd.copy()
    cmap_heat.set_bad(color="#F5F5F5")
    heat_plot = heatmap_in.copy()
    heat_plot[heat_plot == 0] = np.nan
    im_b = ax_b.imshow(heat_plot, aspect="auto", cmap=cmap_heat,
                       vmin=0, vmax=vmax_heat, extent=extent,
                       origin="lower", interpolation="nearest")
    for g in range(1, n_groups):
        ax_b.axhline(
            g * tiles_per_group - 0.5,
            color="#333333",
            lw=0.8,
            ls="--",
            alpha=0.5)
    for g in range(n_groups):
        mid = g * tiles_per_group + tiles_per_group / 2 - 0.5
        ax_b.text(1.003, mid, f"G{g}", ha="left", va="center",
                  transform=ax_b.get_yaxis_transform(),
                  fontsize=FONT_ANNOT, fontweight="bold",
                  color=GRP_COLORS[g % len(GRP_COLORS)], clip_on=False)
    ax_b.set_ylabel("Destination tile", fontsize=FONT_LABEL)
    ax_b.set_title(
        "(b)  Issued memory requests by destination tile over time",
        fontsize=FONT_SUBTITLE,
        fontweight="bold",
        pad=6,
        loc="left")
    cax_b = fig.add_subplot(gs_fig[1, 1])
    cb_b = fig.colorbar(im_b, cax=cax_b)
    cb_b.set_label("Issued requests / window", fontsize=FONT_LABEL - 1)
    cb_b.ax.tick_params(labelsize=FONT_TICK - 1)
    ax_b.tick_params(labelbottom=True)
    ax_b.set_xlabel(x_label, fontsize=FONT_LABEL, labelpad=2)
    ax_b.set_yticks(np.arange(
        0, n_tiles, max(1, tiles_per_group // 2)))

    # (c) Mean load-return latency by locality class.
    ax_c = fig.add_subplot(gs_fig[2, 0], sharex=ax_a)
    system_latency = np.nan_to_num(latency["system"], nan=0.0)
    ax_c.plot(rel_cycle_centers, system_latency, color=COL_REMOTE, lw=2.2,
              zorder=3, label="Overall Avg.")
    for key, color, _, label in display_localities:
        values = np.nan_to_num(latency["locality"][key], nan=0.0)
        line_color = COL_ACCENT if key == "remote" else color
        ax_c.plot(rel_cycle_centers, values, color=line_color, lw=1.8,
                  zorder=4, label=label)
    ax_c.fill_between(
        rel_cycle_centers,
        0,
        system_latency,
        color=COL_REMOTE,
        alpha=0.12)
    ax_c.set_xlim(x_min, x_max)
    ax_c.set_xlabel(x_label, fontsize=FONT_LABEL)
    ax_c.set_ylabel("Latency (cycles; 0 = no returns)", fontsize=FONT_LABEL)
    ax_c.set_title(
        "(c)  Load-return latency over time by locality",
        fontsize=FONT_SUBTITLE,
        fontweight="bold",
        pad=6,
        loc="left")
    ax_c.legend(loc="upper right", fontsize=FONT_LEGEND, ncol=2)
    _clean_spine(ax_c)

    sec_lbl = f"Section {section}" if section is not None else "All sections"
    fig.text(
        0.5, -0.005,
        f"{sec_lbl}  ·  {n_tiles} tiles  ·  {n_windows} windows × "
        f"{timeseries['window_size']} cycles  ·  "
        f"Relative range: 0–{x_max:.0f}  ·  "
        f"Absolute cycle range: "
        f"{cycle_centers[0]:.0f}–{cycle_centers[-1]:.0f}",
        ha="center", fontsize=FONT_ANNOT, color="#666666", style="italic")

    _save(fig, output_dir, "overview_temporal")


# ---------------------------------------------------------------------------
# Load-Return Latency Over Time
# ---------------------------------------------------------------------------

def plot_latency_over_time(timeseries, output_dir, section):
    """Standalone latency figure for cross-design comparison.
    Two panels:
      (a) System-wide average latency + min/max envelope
      (b) Per-group average latency (one line per group)
    """
    cycle_centers = timeseries["cycles"]
    n_windows = timeseries["n_windows"]
    n_groups = timeseries["n_groups"]
    n_tiles = timeseries["n_tiles"]
    tiles_per_group = timeseries["tiles_per_group"]
    sys_avg = timeseries["latency"]["system"]
    grp_avg = timeseries["latency"]["group"]
    tile_avgs = timeseries["latency"]["tile"]
    tile_has_data = np.isfinite(tile_avgs).any(axis=0)
    tile_min = np.full(n_windows, np.nan)
    tile_max = np.full(n_windows, np.nan)
    if tile_has_data.any():
        valid_tile_avgs = tile_avgs[:, tile_has_data]
        tile_min[tile_has_data] = np.nanmin(valid_tile_avgs, axis=0)
        tile_max[tile_has_data] = np.nanmax(valid_tile_avgs, axis=0)

    fig, (ax_a, ax_b) = plt.subplots(2, 1, figsize=(11, 7.5), sharex=True,
                                     gridspec_kw={"hspace": 0.18})

    # (a) System-wide
    ax_a.fill_between(
        cycle_centers,
        tile_min,
        tile_max,
        color=COL_REMOTE,
        alpha=0.12,
        label="Tile min\u2013max range")
    ax_a.plot(cycle_centers, sys_avg, color=COL_REMOTE, lw=2.5,
              label="System average", zorder=3)
    valid = ~np.isnan(sys_avg)
    if valid.any():
        mean_val = np.nanmean(sys_avg)
        ax_a.axhline(mean_val, color=COL_NEUTRAL, lw=1.2, ls=":",
                     alpha=0.6, zorder=1)
        ax_a.text(cycle_centers[valid][-1], mean_val,
                  f"  {mean_val:.1f} cyc", va="bottom", ha="left",
                  fontsize=FONT_ANNOT, color=COL_NEUTRAL, fontstyle="italic")
    ax_a.set_ylabel("Load-return latency (cycles)", fontsize=FONT_LABEL)
    ax_a.set_title(
        "(a)  System-wide average load-return latency",
        fontsize=FONT_SUBTITLE,
        fontweight="bold",
        pad=6,
        loc="left")
    ax_a.legend(loc="upper right", fontsize=FONT_LEGEND)
    _clean_spine(ax_a)

    # (b) Per-group
    for g in range(n_groups):
        valid_g = ~np.isnan(grp_avg[g])
        if not valid_g.any():
            continue
        ax_b.plot(cycle_centers, grp_avg[g],
                  color=GRP_COLORS[g % len(GRP_COLORS)], lw=1.5,
                  solid_capstyle="round", label=f"Group {g}", zorder=3)
    ax_b.set_xlabel("Cycle", fontsize=FONT_LABEL)
    ax_b.set_ylabel("Load-return latency (cycles)", fontsize=FONT_LABEL)
    ax_b.set_title(
        "(b)  Per-group average load-return latency",
        fontsize=FONT_SUBTITLE,
        fontweight="bold",
        pad=6,
        loc="left")
    ax_b.legend(loc="upper right", fontsize=FONT_LEGEND, ncol=2,
                handlelength=3.0, columnspacing=1.5)
    _clean_spine(ax_b)

    x_min = cycle_centers.min() - 20
    x_max = cycle_centers.max() + 20
    ax_a.set_xlim(x_min, x_max)

    sec_lbl = f"Section {section}" if section is not None else "All sections"
    fig.text(
        0.5, -0.005,
        f"{sec_lbl}  ·  {n_groups} groups × "
        f"{tiles_per_group} tiles/group "
        f"({n_tiles} tiles)  ·  "
        f"{n_windows} windows \u00d7 {timeseries['window_size']} cycles",
        ha="center",
        fontsize=FONT_ANNOT, color="#666666", style="italic")

    # Dense time-series lines benefit from a higher export resolution.
    _save(fig, output_dir, "latency_timeseries", dpi=450)


# ---------------------------------------------------------------------------
# Per-Tile Latency Within a Source Group
# ---------------------------------------------------------------------------

def plot_per_tile_group_latency(timeseries, output_dir, section,
                                target_group=0):
    """Plot latency by source tile within one group and its group average."""
    n_windows = timeseries["n_windows"]
    n_tiles = timeseries["n_tiles"]
    tiles_per_group = timeseries["tiles_per_group"]
    grp_tiles = [
        tile for tile in range(n_tiles)
        if tile // tiles_per_group == target_group
    ]
    if not grp_tiles:
        print(f"  [skip] No tiles in group {target_group}")
        return

    cycle_centers = timeseries["group_cycles"][target_group]
    tile_avgs = timeseries["latency"]["tile"][grp_tiles]
    grp_avg = timeseries["latency"]["group"][target_group]

    fig, ax = plt.subplots(figsize=(11, 5.5))

    # Individual tile lines (thin, distinct colors)
    cmap_tiles = plt.cm.tab20(np.linspace(0, 1, len(grp_tiles)))
    for ti, t in enumerate(grp_tiles):
        valid = ~np.isnan(tile_avgs[ti])
        if not valid.any():
            continue
        ax.plot(cycle_centers, tile_avgs[ti],
                color=cmap_tiles[ti], lw=1.2, alpha=0.7,
                solid_joinstyle="round", label=f"Tile {t}", zorder=2)

    # Group average (bold)
    ax.plot(cycle_centers, grp_avg, color="#222222", lw=2.0,
            label=f"Group {target_group} avg", zorder=4)

    # Overall mean reference
    valid_avg = ~np.isnan(grp_avg)
    if valid_avg.any():
        mean_val = np.nanmean(grp_avg)
        ax.axhline(mean_val, color=COL_NEUTRAL, lw=1.2, ls=":",
                   alpha=0.6, zorder=1)
        ax.text(cycle_centers[valid_avg][-1], mean_val,
                f"  {mean_val:.1f} cyc", va="bottom", ha="left",
                fontsize=FONT_ANNOT, color=COL_NEUTRAL, fontstyle="italic")

    ax.set_xlabel("Cycle", fontsize=FONT_LABEL)
    ax.set_ylabel("Load-return latency (cycles)", fontsize=FONT_LABEL)
    ax.set_title(f"Per-source-tile load-return latency — Group {target_group} "
                 f"(tiles {grp_tiles[0]}\u2013{grp_tiles[-1]})",
                 fontsize=FONT_SUBTITLE, fontweight="bold", pad=10)
    leg = ax.legend(loc="upper right", fontsize=FONT_LEGEND - 1, ncol=4,
                    framealpha=0.9, handlelength=2.5)
    for line in leg.get_lines():
        line.set_linewidth(3.0)
    _clean_spine(ax)

    sec_lbl = f"Section {section}" if section is not None else "All sections"
    fig.text(
        0.5, -0.005,
        f"{sec_lbl}  ·  Group {target_group}: "
        f"{len(grp_tiles)} tiles  ·  "
        f"{n_windows} windows \u00d7 {timeseries['window_size']} cycles",
        ha="center",
        fontsize=FONT_ANNOT, color="#666666", style="italic")

    _save(fig, output_dir, f"latency_tile_g{target_group}")


# ---------------------------------------------------------------------------
# Tile-Pair Latency Heatmaps
# ---------------------------------------------------------------------------

class PiecewiseNorm(Normalize):
    """Continuous color normalization with explicit value anchors."""

    def __init__(self, x_points, y_points, vmin=None, vmax=None, clip=False):
        super().__init__(vmin=vmin, vmax=vmax, clip=clip)
        self.x_points = np.asarray(x_points, dtype=float)
        self.y_points = np.asarray(y_points, dtype=float)

    def __call__(self, value, clip=None):
        result, is_scalar = self.process_value(value)
        data = np.asarray(result.data, dtype=float)
        mapped = np.interp(data, self.x_points, self.y_points)
        masked = np.ma.array(mapped, mask=np.ma.getmask(result), copy=False)
        return masked[0] if is_scalar else masked

    def inverse(self, value):
        data = np.asarray(value, dtype=float)
        return np.interp(data, self.y_points, self.x_points)


def _latency_baseline_map(topology):
    """Return topology-specific minima for the load-return metric."""
    n_subgroups = topology.get("n_subgroups_per_group") or 1
    if n_subgroups <= 1:
        return {
            "local": 1.0,
            "same_subgroup": 3.0,
            "same_group": 3.0,
            "remote": 5.0,
        }
    return {
        "local": 1.0,
        "same_subgroup": 3.0,
        "same_group": 5.0,
        "remote": float(topology["remote_group_latency_cycles"]),
    }


def _build_latency_heatmap(pair_data, topology):
    """Build the full-section mean latency matrix and locality map."""
    n_tiles = topology["n_tiles"]
    latencies = np.full((n_tiles, n_tiles), np.nan)
    localities = np.full((n_tiles, n_tiles), "", dtype=object)
    for (source, dest), values in pair_data.items():
        if values["count"] <= 0:
            continue
        latencies[source, dest] = values["lat_sum"] / values["count"]
        localities[source, dest] = values["locality"]
    return latencies, localities


def _render_latency_heatmap(
        image_values,
        annotation_values,
        topology,
        output_dir,
        *,
        title,
        save_name,
        cmap,
        norm,
        colorbar_label,
        colorbar_ticks,
        footer,
        colorbar_ticklabels=None):
    """Render the common tile-pair heatmap frame."""
    n_groups = topology["n_groups"]
    n_tiles = len(image_values)
    tiles_per_group = topology["tiles_per_group"]

    max_px = _matrix_pixel_budget(n_tiles)
    max_w_inches = max_px / DPI - 3.5
    max_h_inches = max_px / DPI - 2.5
    cell_size = min(0.50, max_w_inches / max(n_tiles, 1),
                    max_h_inches / max(n_tiles, 1))
    cell_size = max(cell_size, 0.20)
    fig, ax = plt.subplots(figsize=(n_tiles * cell_size + 3.5,
                                    n_tiles * cell_size + 2.5))
    image = ax.imshow(
        image_values,
        origin="lower",
        cmap=cmap,
        aspect="equal",
        norm=norm,
        interpolation="nearest")

    if n_tiles <= MATRIX_ANNOTATION_LIMIT:
        annotation_size = min(FONT_ANNOT, max(
            2.0, cell_size * 72 * 0.28))
        annotation_weight = "bold" if n_tiles <= 32 else "normal"
        for source in range(n_tiles):
            for dest in range(n_tiles):
                value = annotation_values[source, dest]
                if not np.isnan(value):
                    ax.text(
                        dest, source, f"{value:.0f}", ha="center", va="center",
                        fontsize=annotation_size,
                        fontweight=annotation_weight, color="black")

    source_offsets = {}
    for group in range(n_groups):
        offset = group * tiles_per_group
        if group > 0:
            ax.axhline(offset - 0.5, color="#333333", lw=2.0, alpha=0.7)
        midpoint = offset + tiles_per_group / 2
        group_color = GRP_COLORS[group % len(GRP_COLORS)]
        ax.text(-0.04, midpoint, f"G{group}", ha="right", va="center",
                fontsize=FONT_ANNOT + 3, fontweight="bold", color=group_color,
                transform=ax.get_yaxis_transform(), clip_on=False)
        source_offsets[group] = offset

    dest_offsets = {}
    for group in range(n_groups):
        offset = group * tiles_per_group
        if group > 0:
            ax.axvline(offset - 0.5, color="#333333", lw=2.0, alpha=0.7)
        midpoint = offset + tiles_per_group / 2
        group_color = GRP_COLORS[group % len(GRP_COLORS)]
        ax.text(midpoint, -0.06, f"G{group}", ha="center", va="top",
                fontsize=FONT_ANNOT + 3, fontweight="bold", color=group_color,
                transform=ax.get_xaxis_transform(), clip_on=False)
        dest_offsets[group] = offset

    for group in range(n_groups):
        origin = (dest_offsets[group] - 0.5, source_offsets[group] - 0.5)
        group_color = GRP_COLORS[group % len(GRP_COLORS)]
        for linewidth, color, alpha, zorder in (
                (8.0, "#000000", 0.25, 4),
                (5.0, group_color, 0.5, 5),
                (3.0, group_color, 1.0, 6)):
            ax.add_patch(Rectangle(
                origin, tiles_per_group, tiles_per_group,
                linewidth=linewidth, edgecolor=color, facecolor="none",
                alpha=alpha, zorder=zorder, clip_on=False))

    _add_subgroup_boxes(ax, topology, tiles_per_group, n_groups)

    tick_size = max(6.5, FONT_TICK - 1.5 * (n_tiles > 48))
    ax.set_xticks(range(n_tiles))
    ax.set_yticks(range(n_tiles))
    ax.set_xticklabels(range(n_tiles), fontsize=tick_size, rotation=90)
    ax.set_yticklabels(range(n_tiles), fontsize=tick_size)
    ax.set_xlabel("Destination tile", fontsize=FONT_LABEL, labelpad=20)
    ax.set_ylabel("Source tile", fontsize=FONT_LABEL)
    ax.set_title(title, fontsize=FONT_SUBTITLE, fontweight="bold", pad=10)

    divider = make_axes_locatable(ax)
    colorbar_ax = divider.append_axes("right", size="3.5%", pad=1.00)
    colorbar = fig.colorbar(image, cax=colorbar_ax)
    colorbar.set_label(colorbar_label, fontsize=FONT_LABEL - 1)
    colorbar.set_ticks(colorbar_ticks)
    if colorbar_ticklabels is not None:
        colorbar.set_ticklabels(colorbar_ticklabels)
    colorbar.ax.tick_params(labelsize=FONT_TICK)

    fig.text(0.5, -0.005, footer, ha="center", fontsize=FONT_ANNOT,
             color="#666666", style="italic")
    _save(fig, output_dir, save_name)


def plot_latency_matrix(pair_data, topology, output_dir, section):
    """Full-chip tile×tile heatmap of average measured latency per pair."""
    if not pair_data:
        print("  [skip] No load_return events with latency")
        return

    latencies, _ = _build_latency_heatmap(pair_data, topology)
    n_groups = topology["n_groups"]
    n_tiles = topology["n_tiles"]

    cmap_lat = LinearSegmentedColormap.from_list(
        "lat_GnYlRd", LATENCY_CMAP_COLORS, N=256)
    cmap_lat.set_bad(color="#FFFFFF")
    n_green = 4
    remote_cmap_pos = (
        (n_green - 1) / (len(LATENCY_CMAP_COLORS) - 1))
    contention_multiple = 3.0
    log_cmap_end = 0.95
    tail_multiple = 2.0

    baseline_map = _latency_baseline_map(topology)
    b_local = baseline_map["local"]
    b_sub = baseline_map["same_subgroup"]
    b_remote = baseline_map["remote"]

    vmin_lat = b_local
    # Keep ideal hierarchy baselines green, reserve most of the remaining
    # range for contention up to 3× remote, and the final 5% for the tail.
    vmax_fixed = contention_multiple * b_remote
    vmax_tail = tail_multiple * vmax_fixed

    x_pts = [vmin_lat]
    y_pts = [0.0]
    hierarchy_span = max(b_remote - vmin_lat, 1e-6)
    for bval in (b_local, b_sub):
        if bval > vmin_lat:
            frac = remote_cmap_pos * (bval - vmin_lat) / hierarchy_span
            x_pts.append(bval)
            y_pts.append(frac)
    x_pts.append(b_remote)
    y_pts.append(remote_cmap_pos)
    log_denom = np.log(vmax_fixed / b_remote)
    for i in range(1, 21):
        f = i / 20.0
        x_val = b_remote + f * (vmax_fixed - b_remote)
        y_val = remote_cmap_pos + (
            log_cmap_end - remote_cmap_pos) * np.log(
                x_val / b_remote) / log_denom
        x_pts.append(x_val)
        y_pts.append(y_val)
    tail_span = vmax_tail - vmax_fixed
    for i in range(1, 11):
        f = i / 10.0
        x_pts.append(vmax_fixed + f * tail_span)
        y_pts.append(log_cmap_end + (1.0 - log_cmap_end) * np.sqrt(f))
    lat_norm = PiecewiseNorm(x_pts, y_pts, vmin=vmin_lat, vmax=vmax_tail)

    _tick_vals = sorted(set(
        [int(vmin_lat), int(b_sub), int(b_remote)] +
        list(range(int(b_remote) + 2, int(vmax_fixed), 2)) +
        [int(vmax_fixed), int(vmax_tail)]))
    sec_lbl = f"Section {section}" if section is not None else "All sections"
    n_pairs = len(pair_data)
    total_loads = sum(v["count"] for v in pair_data.values())

    rounded = np.round(latencies)
    clipped = np.clip(rounded, vmin_lat, vmax_tail)
    global_avg = (
        sum(values["lat_sum"] for values in pair_data.values()) /
        max(1, sum(values["count"] for values in pair_data.values())))
    footer = (
        f"{sec_lbl}  ·  {n_tiles} tiles  ·  {n_groups} groups  ·  "
        f"{n_pairs} active pairs  ·  "
        f"{_nice_count(total_loads)} load returns  ·  "
        f"Global avg: {global_avg:.1f} cycles"
    )
    _render_latency_heatmap(
        clipped,
        rounded,
        topology,
        output_dir,
        title="Load-return latency per tile pair (cycles, mean)",
        save_name="latency_matrix",
        cmap=cmap_lat,
        norm=lat_norm,
        colorbar_label="Avg latency (cycles)",
        colorbar_ticks=_tick_vals,
        colorbar_ticklabels=[
            str(tick) if tick < vmax_tail else f"{tick}+"
            for tick in _tick_vals
        ],
        footer=footer)


def plot_latency_over_minimum(pair_data, topology, output_dir, section):
    """Tile-pair latency heatmap normalized by hierarchy-aware ideal minima."""
    if not pair_data:
        print("  [skip] No load_return events with latency")
        return

    latencies, localities = _build_latency_heatmap(pair_data, topology)
    n_groups = topology["n_groups"]
    n_tiles = topology["n_tiles"]

    baseline_map = _latency_baseline_map(topology)

    cmap_delta = LinearSegmentedColormap.from_list(
        "lat_over_minimum", LATENCY_CMAP_COLORS, N=256)
    cmap_delta.set_bad(color="#FFFFFF")

    sec_lbl = f"Section {section}" if section is not None else "All sections"
    n_pairs = len(pair_data)
    total_loads = sum(data["count"] for data in pair_data.values())

    delta_mat = np.full_like(latencies, np.nan, dtype=float)
    for i in range(n_tiles):
        for j in range(n_tiles):
            latency = latencies[i, j]
            if np.isnan(latency):
                continue
            locality = localities[i, j] or "remote"
            delta_mat[i, j] = max(
                0.0,
                latency - baseline_map.get(
                    locality, baseline_map["remote"]))

    delta_mat = np.round(delta_mat)
    valid_delta = delta_mat[~np.isnan(delta_mat)]
    vmax_delta = np.ceil(valid_delta.max()) if len(valid_delta) else 1.0
    vmax_delta = max(1.0, vmax_delta)

    # Expand low excess latencies while compressing the contention tail.
    base_norm = PowerNorm(gamma=0.38, vmin=0.0, vmax=vmax_delta)
    if vmax_delta > 2.0:
        x_points = [0.0, 1.0, min(2.0, vmax_delta)]
        y_points = [float(base_norm(0.0)),
                    float(base_norm(min(1.0, vmax_delta))) * 0.78,
                    float(base_norm(min(2.0, vmax_delta))) * 0.86]
        if vmax_delta > 10.0:
            x_points.extend([5.0, 10.0, vmax_delta])
            y_points.extend([
                float(base_norm(5.0)),
                min(0.97, float(base_norm(10.0)) + 0.10),
                1.0,
            ])
        elif vmax_delta > 5.0:
            x_points.extend([5.0, vmax_delta])
            y_points.extend([float(base_norm(5.0)), 1.0])
        else:
            x_points.append(vmax_delta)
            y_points.append(1.0)
        y_points = np.maximum.accumulate(y_points)
        delta_norm = PiecewiseNorm(
            x_points, y_points, vmin=0.0, vmax=vmax_delta)
    else:
        delta_norm = base_norm

    ticks = sorted(set([0, 1, 2, 5] + [v for v in range(
                   10, int(vmax_delta) + 1, 5)] + [int(vmax_delta)]))
    ticks = [tick for tick in ticks if 0 <= tick <= vmax_delta]
    global_avg_delta = float(
        np.nanmean(valid_delta)) if len(valid_delta) else 0.0
    footer = (
        f"{sec_lbl}  ·  {n_tiles} tiles  ·  {n_groups} groups  ·  "
        f"{n_pairs} active pairs  ·  "
        f"{_nice_count(total_loads)} load returns  ·  "
        f"Global avg excess: {global_avg_delta:.1f} cycles  ·  "
        f"Baselines: local={baseline_map['local']:.0f}, "
        f"same-subgroup={baseline_map['same_subgroup']:.0f}, "
        f"same-group={baseline_map['same_group']:.0f}, "
        f"remote={baseline_map['remote']:.0f}"
    )
    _render_latency_heatmap(
        delta_mat,
        delta_mat,
        topology,
        output_dir,
        title="Excess load-return latency above ideal minimum (mean)",
        save_name="latency_excess_matrix",
        cmap=cmap_delta,
        norm=delta_norm,
        colorbar_label="Excess latency over ideal minimum (cycles)",
        colorbar_ticks=ticks,
        footer=footer)


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

FIGURE_FAMILIES = (
    "matrix",
    "temporal",
    "latency",
    "tile_latency",
    "latency_matrix",
    "latency_over_minimum",
)


def _parse_args(argv=None):
    p = argparse.ArgumentParser(
        description="Analyze communication data and generate traffic and "
                    "latency plots.")
    p.add_argument(
        "result_dir",
        type=Path,
        help="Benchmark result directory")
    p.add_argument("--section", type=int, default=None,
                   help="Section to plot (default: all)")
    p.add_argument("--window", type=int, default=64,
                   help="Time-series bin width in cycles (default: 64)")
    p.add_argument(
        "--figures",
        nargs="+",
        choices=FIGURE_FAMILIES,
        metavar="FAMILY",
        default=None,
        help=f"Figure families to generate: {', '.join(FIGURE_FAMILIES)} "
             "(default: all)")
    args = p.parse_args(argv)
    if args.window <= 0:
        p.error("--window must be positive")
    return args


def main(argv=None):
    args = _parse_args(argv)
    _apply_style()

    result_dir = args.result_dir.resolve()
    events_path = result_dir / "data" / "comm_events_benchmark.csv"
    plots_dir = result_dir / "plots"
    output_dir = plots_dir / "communication"
    overview_dir = plots_dir / "overview"

    if not events_path.is_file():
        sys.exit(f"CSV not found: {events_path}")

    section = args.section
    try:
        topology = load_topology(result_dir / "topology.env")
    except ValueError as exc:
        sys.exit(str(exc))
    n_groups = topology["n_groups"]
    figs = set(args.figures or FIGURE_FAMILIES)

    need_timeseries = bool(
        {"temporal", "latency", "tile_latency"} & figs)
    aggregates = _scan_events(
        _iter_events(events_path, section),
        topology,
    )
    if not aggregates["event_count"]:
        scope = f"section {section}" if section is not None else "the CSV"
        sys.exit(f"No communication events found for {scope}: {events_path}")

    output_dir.mkdir(parents=True, exist_ok=True)
    print(f"Generating communication figures → {output_dir}")

    timeseries = None
    if need_timeseries:
        timeseries = _build_timeseries(
            _iter_events(events_path, section),
            topology,
            args.window,
            aggregates["cycle_bounds"],
        )

    if "matrix" in figs:
        print("\nTraffic matrices …")
        matrices = aggregates["matrices"]
        plot_traffic_matrix_full(matrices, topology, output_dir, section)
        plot_traffic_matrix_group(matrices, topology, output_dir, section)

    if "temporal" in figs and timeseries:
        print("\nTemporal profile …")
        plot_temporal_profile(timeseries, overview_dir, section)

    if "latency" in figs and timeseries:
        print("\nLatency over time …")
        plot_latency_over_time(timeseries, output_dir, section)

    if "tile_latency" in figs and timeseries:
        for tg in range(n_groups):
            print(f"\nPer-tile latency — Group {tg} …")
            plot_per_tile_group_latency(timeseries, output_dir, section,
                                        target_group=tg)

    pair_data = aggregates["pair_data"]

    if "latency_matrix" in figs:
        print("\nTile-pair latency heatmap …")
        plot_latency_matrix(pair_data, topology, output_dir, section)

    if "latency_over_minimum" in figs:
        print("\nLatency above hierarchy minimum …")
        plot_latency_over_minimum(pair_data, topology, output_dir, section)

    print("\nDone.")


if __name__ == "__main__":
    main()
