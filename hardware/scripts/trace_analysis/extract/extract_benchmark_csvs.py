#!/usr/bin/env python3

# Copyright 2026 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Extract both benchmark CSVs in one pass over the traces in a folder.

Each trace is read once. Load/store issues and load returns (with
destinations decoded from the MemPool address map) go to --comm-csv;
per-cycle stall rows (expanded from the stall counters on each retired
instruction) go to --stall-csv. Used by `make benchmark`.

Input: the raw spike-dasm traces in build/traces/, whose `#; { ... }`
annotation dicts carry the per-cycle core signals.

Both output schemas are documented in the README (Data Formats).
"""

from __future__ import annotations

import argparse
import csv
import multiprocessing
import re
import sys
import tempfile
from collections import defaultdict, deque
from pathlib import Path

_root = str(Path(__file__).resolve().parent.parent)
if _root not in sys.path:
    sys.path.insert(0, _root)

from _workflow_metadata import (  # noqa: E402
    derive_topology, describe, load_topology)


# ---------------------------------------------------------------------------
# Trace Format, Output Schemas, and Topology
# ---------------------------------------------------------------------------

_TRACE_IN_REGEX = re.compile(
    r"(\d+)\s+(\d+)\s+(0x[0-9A-Fa-fz]+)\s+([^#;]*)(\s*#;\s*(.*))?"
)
_TRACE_MARKER_REGEX = re.compile(r"^csrwi?\s+trace\s*,")
_RAW_ANNOTATION_REGEX = re.compile(r"'[^']+'\s*:")

_REG_ABI_NAMES_I = (
    "zero", "ra", "sp", "gp", "tp",
    "t0", "t1", "t2",
    "s0", "s1",
    *(f"a{i}" for i in range(8)),
    *(f"s{i}" for i in range(2, 12)),
    *(f"t{i}" for i in range(3, 7)),
)
_LS_SIZE_BYTES = {0: 1, 1: 2, 2: 4, 3: 8}
_MEM_REGION_LABELS = {0: "other", 1: "sequential", 2: "interleaved"}
_IGNORABLE_TRACE_PREFIXES = (
    "## Performance metrics",
    "Performance metrics for section ",
    "Wrote performance metrics to ",
    "Sanity check failed!",
    "total_stalls do not add up.",
)

_COMM_KEYS = [
    "section",
    "cycle",
    "core",
    "group",
    "subgroup",
    "tile",
    "tile_in_group",
    "tile_in_subgroup",
    "core_in_tile",
    "core_in_group",
    "event_type",
    "request_id",
    "pc",
    "insn",
    "origin_pc",
    "origin_insn",
    "rd",
    "size_bytes",
    "address",
    "region",
    "dest_tile",
    "dest_group",
    "dest_subgroup",
    "is_local",
    "is_same_group",
    "is_same_subgroup",
    "issue_cycle",
    "return_cycle",
    "latency",
]

_STALL_KEYS = [
    "core", "group", "tile", "tile_in_group", "core_in_tile",
    "core_in_group", "section", "cycle", "state", "pc", "insn",
    "stall_interval_id", "stall_interval_start", "stall_interval_end",
    "stall_interval_cycles", "stall_interval_offset", "stall_kind",
    "stall_kind_exact", "stall_tot", "stall_ins", "stall_raw",
    "stall_raw_lsu", "stall_raw_acc", "stall_lsu", "stall_acc",
    "stall_wfi",
]


_TOPOLOGY_DEFAULTS = {
    "NUM_CORES": 256, "NUM_GROUPS": 1, "NUM_CORES_PER_TILE": 4,
    "BANKING_FACTOR": 4, "L1_BANK_SIZE": 1024,
    "NUM_SUB_GROUPS_PER_GROUP": 1, "SEQ_MEM_SIZE": 512,
}


def configure(topology=None):
    """Set the topology globals from a metadata dict (defaults otherwise)."""
    global _NUM_CORES, _NUM_GROUPS, _NUM_CORES_PER_TILE, _CORES_PER_GROUP
    global _SEQ_MEM_SIZE, _NUM_TILES, _TILES_PER_GROUP, _TILES_PER_SUBGROUP
    global _INTERLEAVE_STRIDE, _TCDM_SIZE

    values = derive_topology({**_TOPOLOGY_DEFAULTS, **(topology or {})})
    _NUM_CORES = values["n_cores"]
    _NUM_GROUPS = values["n_groups"]
    _NUM_CORES_PER_TILE = values["cores_per_tile"]
    _CORES_PER_GROUP = values["cores_per_group"]
    _SEQ_MEM_SIZE = values["seq_mem_size_per_tile"]
    _NUM_TILES = values["n_tiles"]
    _TILES_PER_GROUP = values["tiles_per_group"]
    _TILES_PER_SUBGROUP = values["tiles_per_subgroup"]
    _INTERLEAVE_STRIDE = values["interleave_stride"]
    _TCDM_SIZE = values["tcdm_size"]


configure()


# ---------------------------------------------------------------------------
# Raw Trace Decoding and Address Mapping
# ---------------------------------------------------------------------------

def _read_annotations(dict_str: str) -> dict:
    """Convert known hex values to integers and retain X-valued fields."""
    annot = {
        key: int(
            val, 16) for key, val in re.findall(
            r"'([^']+)'\s*:\s*(0x[0-9a-fA-F]+)", dict_str)}
    annot.update({
        key: val for key, val in re.findall(
            r"'([^']+)'\s*:\s*(0x[0-9a-fA-FxX]+)",
            re.sub(r"'([^']+)'\s*:\s*(0x[0-9a-fA-F]+)", "", dict_str),
        )
    })
    return annot


def _detect_marker(insn: str) -> bool:
    """Match writes to the trace CSR that delimit benchmark sections."""
    return _TRACE_MARKER_REGEX.match(insn) is not None


def _is_ignorable_trace_line(line: str) -> bool:
    stripped = line.strip()
    if not stripped:
        return True
    if stripped.startswith(_IGNORABLE_TRACE_PREFIXES):
        return True
    key, sep, value = stripped.partition(" ")
    if sep and value and key.replace("_", "").isalnum():
        try:
            float(value)
            return True
        except ValueError:
            return False
    return False


def _format_address(address: int | None) -> str:
    if address is None:
        return ""
    return hex(int(address))


def _reg_name(index: int | None) -> str:
    if index is None or index < 0 or index >= len(_REG_ABI_NAMES_I):
        return ""
    return _REG_ABI_NAMES_I[index]


def _get_core_hierarchy(core_id: int) -> dict:
    if core_id < 0:
        return {
            "group": -1,
            "subgroup": -1,
            "tile": -1,
            "tile_in_group": -1,
            "tile_in_subgroup": -1,
            "core_in_tile": -1,
            "core_in_group": -1,
        }
    tile_id = core_id // _NUM_CORES_PER_TILE
    tile_in_group = tile_id % _TILES_PER_GROUP
    return {
        "group": tile_id // _TILES_PER_GROUP,
        "subgroup": tile_in_group // _TILES_PER_SUBGROUP,
        "tile": tile_id,
        "tile_in_group": tile_in_group,
        "tile_in_subgroup": tile_in_group % _TILES_PER_SUBGROUP,
        "core_in_tile": core_id % _NUM_CORES_PER_TILE,
        "core_in_group": core_id % _CORES_PER_GROUP,
    }


def _addr_to_meta(
        address: int,
        tcdm_address: int | None = None) -> tuple[str, int, int, int]:
    # The logical address selects the memory region; the observed TCDM
    # address selects the actual destination when DAS remaps the request.
    region_code = 0
    dest_tile = -1
    if 0 <= address < _SEQ_MEM_SIZE * _NUM_TILES:
        region_code = 1
        if tcdm_address is None:
            dest_tile = address // _SEQ_MEM_SIZE
        else:
            dest_tile = (tcdm_address // _INTERLEAVE_STRIDE) % _NUM_TILES
    elif 0 <= address < _TCDM_SIZE:
        region_code = 2
        routed_address = address if tcdm_address is None else tcdm_address
        dest_tile = (routed_address // _INTERLEAVE_STRIDE) % _NUM_TILES
    if dest_tile < 0:
        return _MEM_REGION_LABELS[region_code], -1, -1, -1
    dest_group = dest_tile // _TILES_PER_GROUP
    dest_tile_in_group = dest_tile % _TILES_PER_GROUP
    dest_subgroup = dest_tile_in_group // _TILES_PER_SUBGROUP
    return _MEM_REGION_LABELS[region_code], int(
        dest_tile), int(dest_group), int(dest_subgroup)


def _issue_event_type_dict(extras: dict) -> list[dict]:
    events = []
    tcdm_address = (int(extras["tcdm_addr"])
                    if "tcdm_addr" in extras else None)
    if not extras.get("stall") and int(extras.get("is_load", 0)):
        ls_size = int(extras.get("ls_size", 0))
        events.append({
            "event_type": "load_issue",
            "rd_index": int(extras.get("rd", 0)),
            "size_bytes": _LS_SIZE_BYTES.get(ls_size, ""),
            "address": int(extras.get("alu_result", 0)),
            "tcdm_address": tcdm_address,
        })
    elif not extras.get("stall") and int(extras.get("is_store", 0)):
        ls_size = int(extras.get("ls_size", 0))
        events.append({
            "event_type": "store_issue",
            "rd_index": None,
            "size_bytes": _LS_SIZE_BYTES.get(ls_size, ""),
            "address": int(extras.get("alu_result", 0)),
            "tcdm_address": tcdm_address,
        })
    if int(extras.get("retire_load", 0)):
        events.append({
            "event_type": "load_return",
            "rd_index": int(extras.get("lsu_rd", 0)),
            "size_bytes": "",
            "address": None,
            "tcdm_address": None,
        })
    return events


def _parse_line_events(line: str, permissive: bool) -> dict | None:
    line = line.rstrip("\n")
    if _is_ignorable_trace_line(line):
        return None
    match = _TRACE_IN_REGEX.search(line)
    if match is None:
        if permissive:
            return None
        raise ValueError(f"Not a valid trace line:\n{line}")
    _, cycle_str, pc_str, insn, _, extras_str = match.groups()
    events = []
    extras = None
    if extras_str and _RAW_ANNOTATION_REGEX.search(extras_str):
        extras = _read_annotations(extras_str)
        for key in (
            "stall",
            "is_load",
            "is_store",
            "retire_load",
            "rd",
            "lsu_rd",
            "alu_result",
            "ls_size",
            "stall_tot",
            "stall_ins",
            "stall_raw",
            "stall_lsu",
                "stall_acc"):
            extras.setdefault(key, 0)
        events = _issue_event_type_dict(extras)
    insn = insn.strip()
    return {
        "cycle": int(cycle_str),
        "pc": pc_str,
        "insn": insn,
        "events": events,
        "extras": extras,
        "marker": _detect_marker(insn),
    }


# ---------------------------------------------------------------------------
# Communication Row Construction
# ---------------------------------------------------------------------------

def _make_row(
        section: int,
        cycle: int,
        core_id: int,
        hierarchy: dict,
        *,
        event_type: str,
        request_id: int | str,
        pc: str,
        insn: str,
        origin_pc: str,
        origin_insn: str,
        rd_index: int | None,
        size_bytes,
        address: int | None,
        tcdm_address: int | None,
        issue_cycle,
        return_cycle,
        latency):
    region, dest_tile, dest_group, dest_subgroup = _addr_to_meta(
        address, tcdm_address
    ) if address is not None else ("", -1, -1, -1)
    is_local = ""
    is_same_group = ""
    is_same_subgroup = ""
    if dest_tile >= 0:
        is_local = int(dest_tile == hierarchy["tile"])
        is_same_group = int(dest_group == hierarchy["group"])
        is_same_subgroup = int(
            is_same_group and dest_subgroup == hierarchy["subgroup"])
    return {
        "section": section,
        "cycle": cycle,
        "core": core_id,
        "group": hierarchy["group"],
        "subgroup": hierarchy["subgroup"],
        "tile": hierarchy["tile"],
        "tile_in_group": hierarchy["tile_in_group"],
        "tile_in_subgroup": hierarchy["tile_in_subgroup"],
        "core_in_tile": hierarchy["core_in_tile"],
        "core_in_group": hierarchy["core_in_group"],
        "event_type": event_type,
        "request_id": request_id,
        "pc": pc,
        "insn": insn,
        "origin_pc": origin_pc,
        "origin_insn": origin_insn,
        "rd": _reg_name(rd_index),
        "size_bytes": size_bytes,
        "address": _format_address(address),
        "region": region,
        "dest_tile": dest_tile if dest_tile >= 0 else "",
        "dest_group": dest_group if dest_group >= 0 else "",
        "dest_subgroup": dest_subgroup if dest_subgroup >= 0 else "",
        "is_local": is_local,
        "is_same_group": is_same_group,
        "is_same_subgroup": is_same_subgroup,
        "issue_cycle": issue_cycle,
        "return_cycle": return_cycle,
        "latency": latency,
    }


# ---------------------------------------------------------------------------
# Stall Classification and Metadata
# ---------------------------------------------------------------------------

def _raw_stall_sources(extras: dict | None,
                       retired_regs: dict[str, int]) -> set[str]:
    if extras is None or extras.get("stall"):
        return set()
    operands = {int(extras.get(name, 0)) for name in ("rs1", "rs2", "rd")}
    return {
        source for source, register in retired_regs.items()
        if register > 0 and register in operands
    }


def _stall_info_from_extras(extras: dict, cycle: int,
                            prev_wfi_time: int,
                            raw_sources: set[str]) -> dict:
    stall_tot = int(extras["stall_tot"])
    stall_raw = int(extras["stall_raw"])
    return {
        "stall_tot": stall_tot,
        "stall_ins": int(extras["stall_ins"]),
        "stall_raw": stall_raw,
        "stall_raw_lsu": stall_raw if "lsu" in raw_sources else 0,
        "stall_raw_acc": stall_raw if "acc" in raw_sources else 0,
        "stall_lsu": int(extras["stall_lsu"]),
        "stall_acc": int(extras["stall_acc"]),
        "stall_wfi": cycle - prev_wfi_time - 1
        if prev_wfi_time != 0 and stall_tot > 0 else 0,
    }


def _classify_stall(stall_info: dict) -> tuple[str, int]:
    categories = []
    if stall_info["stall_ins"] > 0:
        categories.append("ins")
    if stall_info["stall_raw"] > 0:
        categories.append("raw")
    if stall_info["stall_lsu"] > 0:
        categories.append("lsu")
    if stall_info["stall_acc"] > 0:
        categories.append("acc")
    if stall_info["stall_wfi"] > 0:
        categories.append("wfi")
    if not categories:
        return "none", 1
    return "+".join(categories), int(len(categories) <= 1)


def _add_stall_metadata(row: dict, core_id: int, hierarchy: dict,
                        section: int):
    row["core"] = core_id
    row["group"] = hierarchy["group"]
    row["tile"] = hierarchy["tile"]
    row["tile_in_group"] = hierarchy["tile_in_group"]
    row["core_in_tile"] = hierarchy["core_in_tile"]
    row["core_in_group"] = hierarchy["core_in_group"]
    row["section"] = section


# ---------------------------------------------------------------------------
# Per-Trace Extraction
# ---------------------------------------------------------------------------

def _extract_rows(infile, core_id: int, selected_sections: set,
                  permissive: bool):
    """One pass over a raw trace: communication rows and stall rows."""
    hierarchy = _get_core_hierarchy(core_id)
    pending_loads = defaultdict(deque)
    next_request_id = 0
    section = 0
    prev_wfi_time = 0
    retired_regs = {"lsu": -1, "acc": -1}
    stall_interval_id = 0
    comm_rows = []
    stall_rows = []

    def _selected():
        return not selected_sections or section in selected_sections

    for line in infile:
        parsed = _parse_line_events(line, permissive)
        if parsed is None:
            continue
        extras = parsed["extras"]
        raw_sources = _raw_stall_sources(extras, retired_regs)

        # Emit issues immediately and keep load metadata until its return.
        for event in parsed["events"]:
            if event["event_type"] == "load_issue":
                request_id = next_request_id
                next_request_id += 1
                pending = {
                    "request_id": request_id,
                    "issue_cycle": parsed["cycle"],
                    "pc": parsed["pc"],
                    "insn": parsed["insn"],
                    "rd_index": event["rd_index"],
                    "size_bytes": event["size_bytes"],
                    "address": event["address"],
                    "tcdm_address": event["tcdm_address"],
                }
                if event["rd_index"] is not None:
                    pending_loads[event["rd_index"]].appendleft(pending)
                if _selected():
                    comm_rows.append(_make_row(
                        section,
                        parsed["cycle"],
                        core_id,
                        hierarchy,
                        event_type="load_issue",
                        request_id=request_id,
                        pc=parsed["pc"],
                        insn=parsed["insn"],
                        origin_pc=parsed["pc"],
                        origin_insn=parsed["insn"],
                        rd_index=event["rd_index"],
                        size_bytes=event["size_bytes"],
                        address=event["address"],
                        tcdm_address=event["tcdm_address"],
                        issue_cycle=parsed["cycle"],
                        return_cycle="",
                        latency="",
                    ))

            elif event["event_type"] == "store_issue":
                if _selected():
                    comm_rows.append(_make_row(
                        section,
                        parsed["cycle"],
                        core_id,
                        hierarchy,
                        event_type="store_issue",
                        request_id="",
                        pc=parsed["pc"],
                        insn=parsed["insn"],
                        origin_pc=parsed["pc"],
                        origin_insn=parsed["insn"],
                        rd_index=None,
                        size_bytes=event["size_bytes"],
                        address=event["address"],
                        tcdm_address=event["tcdm_address"],
                        issue_cycle=parsed["cycle"],
                        return_cycle="",
                        latency="",
                    ))

            elif event["event_type"] == "load_return":
                try:
                    pending = pending_loads[event["rd_index"]].pop()
                except IndexError:
                    msg = (
                        f"WARNING: In cycle {parsed['cycle']}, LSU return "
                        f"to {_reg_name(event['rd_index'])} "
                        f"had no matching in-flight load in {infile.name}.")
                    if permissive:
                        print(msg, file=sys.stderr)
                        continue
                    raise SystemExit(msg)
                if _selected():
                    comm_rows.append(_make_row(
                        section,
                        parsed["cycle"],
                        core_id,
                        hierarchy,
                        event_type="load_return",
                        request_id=pending["request_id"],
                        pc=parsed["pc"],
                        insn=parsed["insn"],
                        origin_pc=pending["pc"],
                        origin_insn=pending["insn"],
                        rd_index=event["rd_index"],
                        size_bytes=pending["size_bytes"],
                        address=pending["address"],
                        tcdm_address=pending["tcdm_address"],
                        issue_cycle=pending["issue_cycle"],
                        return_cycle=parsed["cycle"],
                        latency=parsed["cycle"] - pending["issue_cycle"],
                    ))

        # A retired instruction reports counters for the preceding stall
        # interval. Expand them into the per-cycle rows used by the plots.
        if extras is not None and not extras.get("stall"):
            cycle = parsed["cycle"]
            stall_info = _stall_info_from_extras(extras, cycle,
                                                 prev_wfi_time, raw_sources)
            if _selected():
                if stall_info["stall_tot"] > 0:
                    interval_start = cycle - stall_info["stall_tot"]
                    stall_kind, stall_kind_exact = _classify_stall(
                        stall_info)
                    for offset, stall_cycle in enumerate(
                            range(interval_start, cycle)):
                        row = {
                            "cycle": stall_cycle,
                            "state": "stall",
                            "pc": "",
                            "insn": "",
                            "stall_interval_id": stall_interval_id,
                            "stall_interval_start": interval_start,
                            "stall_interval_end": cycle - 1,
                            "stall_interval_cycles":
                                stall_info["stall_tot"],
                            "stall_interval_offset": offset,
                            "stall_kind": stall_kind,
                            "stall_kind_exact": stall_kind_exact,
                        }
                        row.update(stall_info)
                        _add_stall_metadata(row, core_id, hierarchy,
                                            section)
                        stall_rows.append(row)
                    stall_interval_id += 1
                if parsed["insn"]:
                    row = {
                        "cycle": cycle,
                        "state": "issue",
                        "pc": parsed["pc"],
                        "insn": parsed["insn"],
                        "stall_interval_id": "",
                        "stall_interval_start": "",
                        "stall_interval_end": "",
                        "stall_interval_cycles": 0,
                        "stall_interval_offset": "",
                        "stall_kind": "none",
                        "stall_kind_exact": 1,
                        "stall_tot": 0,
                        "stall_ins": 0,
                        "stall_raw": 0,
                        "stall_raw_lsu": 0,
                        "stall_raw_acc": 0,
                        "stall_lsu": 0,
                        "stall_acc": 0,
                        "stall_wfi": 0,
                    }
                    _add_stall_metadata(row, core_id, hierarchy, section)
                    stall_rows.append(row)
            prev_wfi_time = cycle if parsed["insn"] == "wfi" else 0

        # Retiring producers identify the source of later RAW stalls.
        if extras is not None:
            if int(extras.get("retire_load", 0)):
                retired_regs["lsu"] = int(extras.get("lsu_rd", 0))
            if (int(extras.get("retire_acc", 0)) and
                    int(extras.get("acc_pid", 0)) != 0):
                retired_regs["acc"] = int(extras["acc_pid"])
            if not extras.get("stall"):
                retired_regs = {"lsu": -1, "acc": -1}

        # Trace markers delimit the application-defined benchmark sections.
        if parsed["marker"]:
            section += 1

    return comm_rows, stall_rows


# ---------------------------------------------------------------------------
# CSV Output and Parallel Batch Processing
# ---------------------------------------------------------------------------

def _write_rows(rows: list[dict], filename: str, keys: list[str]):
    with Path(filename).open("w", newline="") as out:
        writer = csv.DictWriter(out, keys)
        writer.writeheader()
        writer.writerows(rows)


def _core_id_from_name(filename):
    match = re.search(r"(0x[0-9a-fA-F]+)", filename)
    if match:
        return int(match.group(1), 16)
    match = re.search(r"([\d]+)", filename)
    if match:
        return int(match.group(1))
    return -1


def process_file(trace_path, csv_paths, *, sections=(), permissive=False):
    """Extract one trace and write its rows to the two part CSVs."""
    comm_csv, stall_csv = csv_paths
    core_id = _core_id_from_name(Path(trace_path).name)
    with Path(trace_path).open() as infile:
        comm_rows, stall_rows = _extract_rows(
            infile, core_id, set(sections), permissive)
    _write_rows(comm_rows, comm_csv, _COMM_KEYS)
    _write_rows(stall_rows, stall_csv, _STALL_KEYS)
    return len(comm_rows) + len(stall_rows)


_worker_sections = ()
_worker_permissive = False


def _init_worker(topology, sections, permissive):
    global _worker_sections, _worker_permissive
    configure(topology)
    _worker_sections = sections
    _worker_permissive = permissive


def _process_trace(item):
    trace_path, csv_paths = item
    return process_file(
        trace_path, csv_paths,
        sections=_worker_sections, permissive=_worker_permissive)


def _combine_parts(items, output_paths):
    """Combine per-trace CSV parts in trace order with one header."""
    for output_index, output_path in enumerate(output_paths):
        with output_path.open("w", newline="") as output:
            header_written = False
            for _, part_paths in items:
                part_path = part_paths[output_index]
                if not part_path.exists():
                    continue
                with part_path.open() as part:
                    for line_number, line in enumerate(part):
                        if line_number:
                            output.write(line)
                        elif not header_written:
                            output.write(line)
                            header_written = True


def _run_batch(args, parser):
    folder = Path(args.folder)
    if not folder.is_dir():
        parser.error(f"--folder is not a directory: {folder}")

    output_paths = [Path(args.comm_csv), Path(args.stall_csv)]
    topology_path = (Path(args.topology_env) if args.topology_env
                     else output_paths[0].parent.parent / "topology.env")
    try:
        topology = load_topology(topology_path)
    except ValueError as exc:
        parser.error(str(exc))

    trace_files = sorted(
        path for path in folder.glob("trace_hart_*")
        if path.is_file() and path.suffix != ".dasm")
    if not trace_files:
        parser.error(f"No trace_hart_* files found in {folder}")
    if len(trace_files) != topology["NUM_CORES"]:
        print(f"Warning: found {len(trace_files)} traces, but topology "
              f"expects {topology['NUM_CORES']} cores.", file=sys.stderr)

    for output_path in output_paths:
        if output_path.exists():
            if not args.force:
                parser.error(
                    f"Output CSV already exists: {output_path}\n"
                    "       Use --force to overwrite.")
            output_path.unlink()
        output_path.parent.mkdir(parents=True, exist_ok=True)

    sections = set(args.section or [])

    print(f"Topology: {describe(topology)}", file=sys.stderr)
    jobs = min(args.jobs, len(trace_files))
    print(f"Extracting {len(trace_files)} traces with {jobs} workers ...",
          file=sys.stderr)

    with tempfile.TemporaryDirectory(prefix="benchmark_par_") as temp_dir:
        temp_dir = Path(temp_dir)
        items = [
            (trace_path, (
                temp_dir / f"comm_{index:04d}.csv",
                temp_dir / f"stall_{index:04d}.csv"))
            for index, trace_path in enumerate(trace_files)
        ]
        done = 0
        with multiprocessing.Pool(
                jobs, initializer=_init_worker,
                initargs=(topology, sections, args.permissive)) as pool:
            for _ in pool.imap_unordered(_process_trace, items):
                done += 1
                if done % 64 == 0 or done == len(trace_files):
                    print(f"Processed {done}/{len(trace_files)} traces",
                          file=sys.stderr)
        _combine_parts(items, output_paths)


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main(argv=None):
    parser = argparse.ArgumentParser(
        description="Extract the communication-event and stall "
                    "time-series CSVs from all traces in a folder.")
    parser.add_argument(
        "--folder", required=True,
        help="Folder containing trace_hart_* files")
    parser.add_argument(
        "--comm-csv", required=True,
        help="Combined communication-events CSV output path")
    parser.add_argument(
        "--stall-csv", required=True,
        help="Combined stall time-series CSV output path")
    section = parser.add_mutually_exclusive_group()
    section.add_argument(
        "--section", type=int, action="append",
        help="Emit rows only for the specified section; may be repeated")
    section.add_argument(
        "--benchmark-only", action="store_const", const=[1], dest="section",
        help="Shortcut for --section 1 for apps with a single "
             "benchmark bracket")
    parser.add_argument(
        "-p", "--permissive", action="store_true",
        help="Ignore malformed non-trace lines when possible")
    parser.add_argument(
        "--force", action="store_true",
        help="Overwrite existing CSV output (default: refuse)")
    parser.add_argument(
        "--topology-env",
        help="Path to topology.env (default: next to the output data dir)")
    parser.add_argument(
        "-j", "--jobs", type=int, default=16,
        help="Number of parallel extraction workers (default: 16)")
    args = parser.parse_args(argv)

    _run_batch(args, parser)
    print(f"Wrote communication events to {args.comm_csv}")
    print(f"Wrote stall time-series to {args.stall_csv}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
