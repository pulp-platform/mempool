#!/usr/bin/env python3

# Copyright 2026 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Data loading, aggregation, and rendering for the stall plots."""

import csv
from pathlib import Path

import matplotlib.pyplot as plt
import numpy as np
from matplotlib.lines import Line2D
from matplotlib.patches import Patch
from matplotlib.ticker import MaxNLocator


# ---------------------------------------------------------------------------
# Data Loading and Labels
# ---------------------------------------------------------------------------

STALL_CATEGORIES = ["ins", "raw", "lsu", "acc", "wfi", "other"]
STALL_COLORS = {
    "issue": "#78C679", "stall": "#D9D9D9",
    "ins": "#4C78A8", "raw": "#F58518", "lsu": "#17BECF",
    "acc": "#E45756", "wfi": "#B279A2", "other": "#9D755D",
}
STALL_LABELS = {
    "issue": "Issuing", "stall": "Stalled",
    "ins": "Instruction fetch", "raw": "RAW", "lsu": "LSU",
    "acc": "Accelerator", "wfi": "WFI", "other": "Other / mixed",
}


def stall_label(category):
    return STALL_LABELS.get(category, category)


def _int(value):
    return None if value is None or value == "" else int(value)


def load_rows(csv_path):
    rows = []
    with Path(csv_path).open(newline="") as csv_file:
        for row in csv.DictReader(csv_file):
            rows.append({
                "core": _int(row.get("core")),
                "group": _int(row.get("group")),
                "tile": _int(row.get("tile")),
                "section": _int(row.get("section")),
                "cycle": _int(row.get("cycle")),
                "state": (row.get("state") or "").strip(),
                "stall_kind": (row.get("stall_kind") or "").strip(),
            })
    return rows


def filter_rows(rows, *, section=None, group=None, tile=None, core=None):
    """Filter rows by optional sets of section/group/tile/core IDs."""
    filters = {}
    if section:
        filters["section"] = set(section)
    if group:
        filters["group"] = set(group)
    if tile:
        filters["tile"] = set(tile)
    if core:
        filters["core"] = set(core)
    if not filters:
        return rows
    return [row for row in rows
            if all(row[name] in values for name, values in filters.items())]


def split_stall_kind(kind):
    if not kind or kind == "none":
        return ["other"]
    categories = [
        part.strip() if part.strip() in STALL_CATEGORIES else "other"
        for part in kind.split("+") if part.strip()
    ]
    return categories or ["other"]


# ---------------------------------------------------------------------------
# Shared Plot Helpers
# ---------------------------------------------------------------------------

def set_cycle_ticks(ax, positions, labels=None, max_ticks=25):
    """Place x ticks at nice round cycle values."""
    if len(positions) <= 1:
        return
    labels = positions if labels is None else labels
    low, high = float(labels[0]), float(labels[-1])
    span = high - low
    if span <= 0:
        return

    raw_step = span / max_ticks
    magnitude = 10 ** int(np.floor(np.log10(max(raw_step, 1))))
    for multiplier in (1, 2, 5, 10, 20, 50, 100):
        step = magnitude * multiplier
        if span / step <= max_ticks:
            break

    first = int(np.ceil(low / step)) * step
    nice_values = np.unique(np.concatenate((
        [low], np.arange(first, high + 1, step), [high])))
    label_values = np.array(labels, dtype=float)
    tick_positions = []
    tick_labels = []
    for value in nice_values:
        index = int(np.argmin(np.abs(label_values - value)))
        tick_positions.append(positions[index])
        tick_labels.append(str(int(label_values[index])))

    min_gap = step * 0.45
    filtered_positions = [tick_positions[0]]
    filtered_labels = [tick_labels[0]]
    for position, label in zip(tick_positions[1:], tick_labels[1:]):
        if abs(int(label) - int(filtered_labels[-1])) >= min_gap:
            filtered_positions.append(position)
            filtered_labels.append(label)
    ax.set_xticks(filtered_positions)
    ax.set_xticklabels(filtered_labels)


def plot_categories_current(
        ax, cycles, category_values, present, title,
        ylabel="Stalled cores"):
    """Plot active stall categories as a stacked area."""
    arrays = [category_values[category] for category in present]
    ax.stackplot(
        cycles,
        arrays,
        labels=[stall_label(category) for category in present],
        colors=[STALL_COLORS[category] for category in present],
        alpha=0.85,
        step="post")
    total = np.sum(np.vstack(arrays), axis=0) if arrays else np.zeros_like(
        cycles)
    maximum = float(np.max(total)) if len(total) else 0
    ax.set_xlim(cycles[0], cycles[-1])
    ax.set_ylim(0, max(1.0, maximum * 1.08))
    ax.yaxis.set_major_locator(MaxNLocator(integer=True))
    ax.set_title(title)
    ax.set_ylabel(ylabel)
    ax.grid(True, axis="y", alpha=0.25)
    ax.legend(loc="upper left", frameon=True, fancybox=True,
              edgecolor="#CCCCCC", facecolor="white", framealpha=0.68,
              handleheight=1.1, handlelength=2.5)


def plot_categories_cumulative(
        ax, cycles, category_values, present, title):
    """Plot active stall categories as cumulative lines."""
    legend_handles = []
    for category in present:
        values = category_values[category]
        ax.plot(cycles, values, color=STALL_COLORS[category],
                lw=2.0, label=stall_label(category))
        rising = np.diff(values, prepend=values[0]) > 0
        ax.fill_between(cycles, 0, values, where=rising,
                        color=STALL_COLORS[category], alpha=0.22)
        legend_handles.append(Line2D(
            [0], [0], color=STALL_COLORS[category], linewidth=4.0,
            label=stall_label(category)))
    maximum = max((float(np.max(category_values[category]))
                   for category in present), default=0)
    ax.set_xlim(cycles[0], cycles[-1])
    ax.set_ylim(0, max(1.0, maximum * 1.05))
    ax.set_title(title)
    ax.set_ylabel("Accumulated core-cycles")
    ax.grid(True, axis="y", alpha=0.25)
    ax.legend(handles=legend_handles, loc="upper left", frameon=True,
              fancybox=True, edgecolor="#CCCCCC", facecolor="white",
              framealpha=0.9, handleheight=1.1, handlelength=3.0)


# ---------------------------------------------------------------------------
# Overview Time-Series Aggregation
# ---------------------------------------------------------------------------

def aggregate_rows(rows, window, context_field="tile"):
    """Bin cluster issue and stall activity for the workload overview."""
    min_cycle = min(r["cycle"] for r in rows)
    max_cycle = max(r["cycle"] for r in rows)
    nw = (max_cycle - min_cycle) // window + 1

    issue = np.zeros(nw)
    stall = np.zeros(nw)
    mix = {c: np.zeros(nw) for c in STALL_CATEGORIES}
    ctxs = {}

    for r in rows:
        wi = (r["cycle"] - min_cycle) // window
        cv = r[context_field]
        if cv not in ctxs:
            ctxs[cv] = {
                "issue": np.zeros(nw), "stall": np.zeros(nw),
                "mix": {c: np.zeros(nw) for c in STALL_CATEGORIES},
            }
        if r["state"] == "issue":
            issue[wi] += 1
            ctxs[cv]["issue"][wi] += 1
        else:
            stall[wi] += 1
            ctxs[cv]["stall"][wi] += 1
            cats = split_stall_kind(r["stall_kind"])
            w = 1.0 / len(cats)
            for c in cats:
                mix[c][wi] += w
                ctxs[cv]["mix"][c][wi] += w

    x_centers = np.array(
        [min_cycle + i * window + window / 2.0 for i in range(nw)])
    wf = float(window)
    cvs = sorted(ctxs)
    ctx_issue = np.array([ctxs[v]["issue"] / wf for v in cvs])
    ctx_stall = np.array([ctxs[v]["stall"] / wf for v in cvs])

    return {
        "window": window, "min_cycle": min_cycle, "max_cycle": max_cycle,
        "num_windows": nw, "x_centers": x_centers,
        "overall": {
            "issue_count": issue / wf,
            "stall_count": stall / wf,
            "stall_reason_count": {c: v / wf for c, v in mix.items()},
        },
        "context_values": cvs,
        "context_issue_count": ctx_issue,
        "context_stall_count": ctx_stall,
    }


# ---------------------------------------------------------------------------
# Tile-Detail Aggregation
# ---------------------------------------------------------------------------

def build_tile_series(rows, tile_id):
    """Build per-cycle and cumulative data for one tile-detail figure."""
    tile_rows = [r for r in rows if r["tile"] == tile_id]
    if not tile_rows:
        raise ValueError(f"No rows for tile {tile_id}")

    cycles = np.array(sorted({r["cycle"] for r in tile_rows}), dtype=int)
    c2i = {int(c): i for i, c in enumerate(cycles)}
    n = len(cycles)
    issue_cur = np.zeros(n)
    stall_cur = np.zeros(n)
    cat_cur = {c: np.zeros(n) for c in STALL_CATEGORIES}

    cores = sorted({r["core"] for r in tile_rows})
    core2i = {cid: i for i, cid in enumerate(cores)}
    per_core_state = np.zeros((len(cores), n))

    cat_index = {c: i for i, c in enumerate(
        STALL_CATEGORIES)}  # ins=0..other=5
    for r in tile_rows:
        ci = c2i[r["cycle"]]
        if r["state"] == "issue":
            issue_cur[ci] += 1
            per_core_state[core2i[r["core"]], ci] = 1.0
        else:
            stall_cur[ci] += 1
            cats_hit = split_stall_kind(r["stall_kind"])
            w = 1.0 / len(cats_hit)
            for cat in cats_hit:
                cat_cur[cat][ci] += w
            # Combined stalls use the first category in the heatmap (2–7).
            per_core_state[core2i[r["core"]], ci] = (
                2.0 + cat_index[cats_hit[0]])

    present = [c for c in STALL_CATEGORIES if np.any(cat_cur[c] > 0)]
    return {
        "tile_id": tile_id,
        "cores": cores,
        "per_core_state": per_core_state,
        "cycles": cycles,
        "issue_current": issue_cur,
        "stall_current": stall_cur,
        "issue_cumulative": np.cumsum(issue_cur),
        "stall_cumulative": np.cumsum(stall_cur),
        "category_current": cat_cur,
        "category_cumulative": {
            c: np.cumsum(v) for c,
            v in cat_cur.items()},
        "present_categories": present,
    }


# ---------------------------------------------------------------------------
# Overview Figures
# ---------------------------------------------------------------------------

def _agg_ticks(ax, agg, max_ticks=12):
    set_cycle_ticks(
        ax,
        np.arange(
            agg["num_windows"]),
        agg["x_centers"],
        max_ticks)


def write_overview_page(path, agg, filter_desc, window):
    """Plot progress, stall composition, and per-tile stall fraction."""
    fig = plt.figure(figsize=(16, 12), constrained_layout=True)
    gs = fig.add_gridspec(2, 2, height_ratios=[1, 1.3])
    ax_prog = fig.add_subplot(gs[0, 0])
    ax_mix = fig.add_subplot(gs[0, 1])
    ax_hm = fig.add_subplot(gs[1, :])

    # 1 — progress
    x = np.arange(agg["num_windows"])
    ic = agg["overall"]["issue_count"]
    sc = agg["overall"]["stall_count"]
    ax_prog.plot(x, ic, color=STALL_COLORS["issue"], lw=2.5, label="Issuing")
    ax_prog.fill_between(x, 0, ic, color=STALL_COLORS["issue"], alpha=0.18)
    ax_prog.plot(x, sc, color="#4d4d4d", lw=2.0, label="Stalled")
    ax_prog.fill_between(x, 0, sc, color="#4d4d4d", alpha=0.10)
    ax_prog.set_ylim(
        0, max(1.0, float(np.nanmax([ic.max(), sc.max()])) * 1.08))
    ax_prog.set_title("1. Progress: issuing vs stalled cores")
    ax_prog.set_ylabel("Cores")
    ax_prog.grid(True, axis="y", alpha=0.25)
    _agg_ticks(ax_prog, agg)
    ax_prog.legend(loc="upper right", frameon=True, fancybox=True,
                   edgecolor="#CCCCCC", facecolor="white", framealpha=0.9,
                   ncol=2, handleheight=1.7, handlelength=2.5)

    # 2 — stall composition
    arrays = [agg["overall"]["stall_reason_count"][c]
              for c in STALL_CATEGORIES]
    colors = [STALL_COLORS[c] for c in STALL_CATEGORIES]
    ax_mix.stackplot(
        x,
        arrays,
        labels=[
            stall_label(c) for c in STALL_CATEGORIES],
        colors=colors,
        alpha=0.95)
    total = np.sum(np.vstack(arrays), axis=0)
    ax_mix.set_ylim(0, max(1.0, float(np.nanmax(total)) * 1.08))
    ax_mix.set_title("2. Stall composition by cause")
    ax_mix.set_ylabel("Stalled cores")
    ax_mix.grid(True, axis="y", alpha=0.25)
    _agg_ticks(ax_mix, agg)
    ax_mix.legend(loc="upper right", ncol=3, frameon=True, fancybox=True,
                  edgecolor="#CCCCCC", facecolor="white", framealpha=0.9,
                  handleheight=1.7, handlelength=2.5)

    # 3 — stall fraction for tiles with observed activity
    all_activity = agg["context_issue_count"] + agg["context_stall_count"]
    active_mask = np.any(all_activity > 0, axis=1)
    active_indices = np.where(active_mask)[0]
    if len(active_indices) == 0:
        active_indices = np.arange(len(agg["context_values"]))
    active_labels = [str(agg["context_values"][i]) for i in active_indices]

    issue_mat = agg["context_issue_count"][active_indices, :]
    stall_mat = agg["context_stall_count"][active_indices, :]
    total_mat = issue_mat + stall_mat
    with np.errstate(divide="ignore", invalid="ignore"):
        stall_frac = np.where(total_mat > 0, stall_mat / total_mat, np.nan)

    img = ax_hm.imshow(stall_frac, aspect="auto", interpolation="nearest",
                       cmap="RdYlGn_r", vmin=0, vmax=1, origin="lower")
    ax_hm.set_facecolor("#E0E0E0")
    ax_hm.set_title(
        "3. Per-tile stall fraction (green = issuing, red = stalled)")
    ax_hm.set_ylabel("Tile")
    ax_hm.set_xlabel("Cycle")
    _agg_ticks(ax_hm, agg)
    n_active = len(active_indices)
    if n_active <= 32:
        ax_hm.set_yticks(np.arange(n_active))
        ax_hm.set_yticklabels(active_labels)
    else:
        step = max(1, n_active // 16)
        shown = list(range(0, n_active, step))
        if (n_active - 1) not in shown:
            shown.append(n_active - 1)
        ax_hm.set_yticks(shown)
        ax_hm.set_yticklabels([active_labels[i] for i in shown])
    cbar = fig.colorbar(img, ax=ax_hm, fraction=0.028, pad=0.02)
    cbar.set_label("Stall fraction")
    cbar.set_ticks([0, 0.25, 0.5, 0.75, 1.0])
    cbar.set_ticklabels(["0%\n(all issuing)", "25%",
                        "50%", "75%", "100%\n(all stalled)"])

    fig.suptitle("Cluster Stall Overview", fontsize=17, fontweight="bold")
    fig.text(0.01, -0.005,
             f"Reconstructed from annotated traces, not a true cycle logger. "
             f"Filters: {filter_desc}. Window={window} cycles.",
             fontsize=9, alpha=0.82, va="top")
    fig.savefig(path, dpi=96, bbox_inches="tight")
    plt.close(fig)


def build_group_overview_stats(rows):
    """Aggregate issue/stall/core-cycle statistics by group."""
    if not rows:
        raise ValueError("No rows for group overview")

    groups = sorted({row["group"]
                    for row in rows if row.get("group") is not None})
    min_cycle = min(row["cycle"] for row in rows)
    max_cycle = max(row["cycle"] for row in rows)
    elapsed_cycles = max(1, max_cycle - min_cycle + 1)
    stats = {
        group: {
            "issue": 0.0,
            "stall": 0.0,
            "mix": {category: 0.0 for category in STALL_CATEGORIES},
        }
        for group in groups
    }

    for row in rows:
        group = row.get("group")
        if group not in stats:
            continue
        if row["state"] == "issue":
            stats[group]["issue"] += 1.0
        else:
            stats[group]["stall"] += 1.0
            cats = split_stall_kind(row["stall_kind"])
            weight = 1.0 / len(cats)
            for category in cats:
                stats[group]["mix"][category] += weight

    return {
        "groups": groups,
        "elapsed_cycles": elapsed_cycles,
        "stats": stats,
    }


def _annotate_stacked_barh(ax, left, width, y, total, label):
    if total <= 0 or width / total <= 0.04:
        return
    pct = width / total * 100.0
    text = f"{pct:.1f}%"
    if width / total > 0.10:
        text = f"{label}\n{pct:.1f}%\n{int(width)} cyc."
    ax.text(left + width / 2, y, text, ha="center", va="center",
            fontsize=9, fontweight="bold", color="white")


def write_group_overview_page(path, group_stats, filter_desc):
    """Plot per-group IPC and issuing/stalled core-cycle breakdowns."""
    groups = group_stats["groups"]
    stats = group_stats["stats"]
    elapsed_cycles = group_stats["elapsed_cycles"]
    y = np.arange(len(groups))

    issue_vals = np.array([stats[group]["issue"]
                          for group in groups], dtype=float)
    stall_vals = np.array([stats[group]["stall"]
                          for group in groups], dtype=float)
    totals = issue_vals + stall_vals
    ipc_vals = np.divide(
        issue_vals,
        totals,
        out=np.zeros_like(issue_vals),
        where=totals > 0)

    fig, axes = plt.subplots(3, 1, figsize=(15, 12), constrained_layout=True,
                             gridspec_kw={"height_ratios": [1.0, 1.15, 1.35]})
    ax_ipc, ax_state, ax_mix = axes

    # 1. Group IPC.
    ax_ipc.bar(y, ipc_vals, color=STALL_COLORS["issue"], edgecolor="white",
               linewidth=0.7)
    ax_ipc.set_xticks(y)
    ax_ipc.set_xticklabels([f"Group {group}" for group in groups])
    ax_ipc.set_ylabel("Instructions / core-cycle")
    ax_ipc.set_title("1. Group average per-core IPC")
    ax_ipc.grid(True, axis="y", alpha=0.25)
    ax_ipc.set_ylim(0, 1)
    for xpos, value in zip(y, ipc_vals):
        ax_ipc.text(xpos, value, f"{value:.2f}", ha="center", va="bottom",
                    fontsize=9, fontweight="bold", color="#333333")

    # 2. Issue/stall cycle split, with stall causes expanded in-place.
    left = np.zeros(len(groups))
    ax_state.barh(y, issue_vals, left=left, color=STALL_COLORS["issue"],
                  edgecolor="white", linewidth=0.5, label="Issuing")
    for idx, width in enumerate(issue_vals):
        _annotate_stacked_barh(
            ax_state,
            left[idx],
            width,
            y[idx],
            totals[idx],
            "Issuing")
    left += issue_vals

    for category in STALL_CATEGORIES:
        values = np.array([stats[group]["mix"][category]
                          for group in groups], dtype=float)
        ax_state.barh(
            y,
            values,
            left=left,
            color=STALL_COLORS[category],
            edgecolor="white",
            linewidth=0.5,
            label=stall_label(category))
        for idx, width in enumerate(values):
            _annotate_stacked_barh(
                ax_state,
                left[idx],
                width,
                y[idx],
                totals[idx],
                stall_label(category))
        left += values

    ax_state.set_yticks(y)
    ax_state.set_yticklabels([f"Group {group}" for group in groups])
    ax_state.set_xlabel("Core-cycles")
    ax_state.set_title("2. Core-cycle breakdown: issuing and stall causes")
    ax_state.grid(True, axis="x", alpha=0.25)
    ax_state.legend(loc="center left", bbox_to_anchor=(1.005, 0.5), ncol=1,
                    frameon=True, fancybox=True,
                    edgecolor="#CCCCCC", facecolor="white", framealpha=0.9,
                    handleheight=1.15, handlelength=2.5)

    # 3. Stall breakdown by reason.
    left = np.zeros(len(groups))
    for category in STALL_CATEGORIES:
        values = np.array([stats[group]["mix"][category]
                          for group in groups], dtype=float)
        ax_mix.barh(
            y,
            values,
            left=left,
            color=STALL_COLORS[category],
            edgecolor="white",
            linewidth=0.5,
            label=stall_label(category))
        for idx, width in enumerate(values):
            _annotate_stacked_barh(
                ax_mix, left[idx], width, y[idx], max(
                    stall_vals[idx], 1.0), stall_label(category))
        left += values
    ax_mix.set_yticks(y)
    ax_mix.set_yticklabels([f"Group {group}" for group in groups])
    ax_mix.set_xlabel("Stalled core-cycles")
    ax_mix.set_title("3. Stall breakdown by cause")
    ax_mix.grid(True, axis="x", alpha=0.25)
    ax_mix.legend(loc="center left", bbox_to_anchor=(1.005, 0.5), ncol=1,
                  frameon=True, fancybox=True,
                  edgecolor="#CCCCCC", facecolor="white", framealpha=0.9,
                  handleheight=1.15, handlelength=2.5)

    fig.suptitle(
        "Per-Group IPC and Core-Cycle Breakdown",
        fontsize=17,
        fontweight="bold")
    fig.text(
        0.01, -0.005,
        f"Filters: {filter_desc}. "
        f"IPC = issuing core-cycles / observed core-cycles; "
        f"elapsed section span={elapsed_cycles} cycles.", fontsize=9,
        alpha=0.82, va="top")
    fig.savefig(path, dpi=96, bbox_inches="tight")
    plt.close(fig)


# ---------------------------------------------------------------------------
# Tile-Detail Figure
# ---------------------------------------------------------------------------

def write_tile_detail(png_path, ts):
    """All-in-one tile detail figure.

    Subplot order (top to bottom):
      1. Per-core state heatmap (stall subtypes)
      2. Core-cycle breakdown bar
      3. Current stall causes
      4. Cumulative stall causes
    """
    tid = ts["tile_id"]
    cycles = ts["cycles"]
    cats = ts["present_categories"]

    nrows = 4
    ratios = [1.2, 0.8, 1.5, 1.5]
    fig, axes = plt.subplots(nrows, 1, figsize=(20, 29),
                             gridspec_kw={"height_ratios": ratios},
                             constrained_layout=True)
    row = 0

    # ── 1. per-core state heatmap (stall subtype colours) ────────────────
    n_cats = len(STALL_CATEGORIES)  # 6
    hm_colors = ["#FFFFFF", STALL_COLORS["issue"]] + \
        [STALL_COLORS[c] for c in STALL_CATEGORIES]
    hm_cmap = plt.matplotlib.colors.ListedColormap(hm_colors)
    axes[row].imshow(
        ts["per_core_state"],
        aspect="auto",
        interpolation="nearest",
        cmap=hm_cmap,
        vmin=0,
        vmax=1 + n_cats,
        origin="lower")
    axes[row].set_title("Per-Core Execution State by Stall Cause")
    axes[row].set_ylabel("Core in tile")
    axes[row].set_yticks(np.arange(len(ts["cores"])))
    axes[row].set_yticklabels([str(c) for c in ts["cores"]])
    axes[row].set_yticks(np.arange(-0.5, len(ts["cores"]), 1.0), minor=True)
    axes[row].grid(which="minor", axis="y", color="#F2F2F2", linewidth=2.0)
    axes[row].tick_params(which="minor", left=False)
    set_cycle_ticks(axes[row], np.arange(len(cycles)), cycles)
    hm_handles = [Patch(facecolor=STALL_COLORS["issue"], edgecolor="black",
                        linewidth=0.5, label="Issuing")] + \
        [Patch(facecolor=STALL_COLORS[c], edgecolor="black", linewidth=0.5,
               label=stall_label(c)) for c in cats]
    axes[row].legend(handles=hm_handles, loc="lower left",
                     bbox_to_anchor=(0, 1.02), frameon=True, fancybox=True,
                     edgecolor="#CCCCCC", facecolor="white", framealpha=0.9,
                     ncol=len(hm_handles),
                     handleheight=1.15, handlelength=2.5)
    axes[row].set_xlabel("Cycle")
    row += 1

    # ── 2. stacked horizontal bar: summed core-cycle breakdown ───────────
    total = float(ts["issue_cumulative"][-1] + ts["stall_cumulative"][-1])
    bar_labels = ["Issuing"] + [stall_label(c) for c in cats]
    bar_values = [float(ts["issue_cumulative"][-1])] + \
        [float(ts["category_cumulative"][c][-1]) for c in cats]
    bar_colors = [STALL_COLORS["issue"]] + [STALL_COLORS[c] for c in cats]

    ax_bar = axes[row]
    left = 0.0
    for lbl, val, col in zip(bar_labels, bar_values, bar_colors):
        pct = val / total * 100 if total else 0
        count_text = f"{int(val)} cyc."
        ax_bar.barh(
            "Core-cycles",
            val,
            left=left,
            color=col,
            edgecolor="white",
            linewidth=0.5,
            label=f"{lbl} ({pct:.1f}%)")
        if val / total > 0.10:
            ax_bar.text(
                left + val / 2,
                0,
                f"{lbl}\n{pct:.1f}%\n{count_text}",
                ha="center",
                va="center",
                fontsize=9,
                fontweight="bold",
                color="white")
        elif val / total > 0.04:
            medium_text = f"{pct:.1f}%\n{count_text}"
            ax_bar.text(
                left + val / 2,
                0,
                medium_text,
                ha="center",
                va="center",
                fontsize=9,
                fontweight="bold",
                color="white")
        left += val
    ax_bar.set_xlim(0, total)
    ax_bar.set_xlabel("Core-cycle amount")
    ax_bar.set_title(
        f"Tile Summed Core-Cycle Breakdown  ({int(total)} total "
        f"core-cycles across {len(ts['cores'])} cores)")
    ax_bar.legend(
        loc="upper left",
        frameon=True,
        fancybox=True,
        edgecolor="#CCCCCC",
        facecolor="white",
        framealpha=0.9,
        ncol=1,
        handleheight=1.15,
        handlelength=2.5)
    row += 1

    # ── 3. current stall causes ──────────────────────────────────────────
    plot_categories_current(axes[row], cycles, ts["category_current"], cats,
                            "Current Stall Causes",
                            ylabel="Total stalled cores")
    axes[row].set_xlabel("Cycle")
    set_cycle_ticks(axes[row], cycles)
    row += 1

    # ── 4. cumulative stall causes ───────────────────────────────────────
    plot_categories_cumulative(
        axes[row],
        cycles,
        ts["category_cumulative"],
        cats,
        "Cumulative Stall Causes")
    axes[row].set_xlabel("Cycle")
    set_cycle_ticks(axes[row], cycles)
    row += 1

    fig.suptitle(f"Tile {tid} Detail Report", fontsize=17, fontweight="bold")

    fig.savefig(png_path, dpi=96, bbox_inches="tight")
    plt.close(fig)
