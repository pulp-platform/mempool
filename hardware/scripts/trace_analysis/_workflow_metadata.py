#!/usr/bin/env python3

# Copyright 2026 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""topology.env is the single source of truth for the machine shape.

`make benchmark` writes it into every result directory from the same
make variables that configured the RTL. To analyze foreign data, write
the file by hand: one KEY=value per line, all TOPOLOGY_KEYS required
(see the README).
"""

from __future__ import annotations

from pathlib import Path

TOPOLOGY_KEYS = (
    'NUM_CORES',
    'NUM_GROUPS',
    'NUM_CORES_PER_TILE',
    'SEQ_MEM_SIZE',
    'BANKING_FACTOR',
    'L1_BANK_SIZE',
    'NUM_SUB_GROUPS_PER_GROUP',
)
# Historical default from config.mk for older topology files.
OPTIONAL_TOPOLOGY_DEFAULTS = {
    'REMOTE_GROUP_LATENCY_CYCLES': 7,
}


def derive_topology(topology) -> dict:
    """Return topology metadata with its common derived geometry."""
    topology = dict(topology)
    values = {key: int(topology[key]) for key in TOPOLOGY_KEYS}
    values.update({
        key: int(topology.get(key, default))
        for key, default in OPTIONAL_TOPOLOGY_DEFAULTS.items()
    })
    invalid = [f'{key}={value}' for key, value in values.items()
               if value <= 0]
    if invalid:
        raise ValueError(
            f'Topology values must be positive: {", ".join(invalid)}')

    n_cores = values['NUM_CORES']
    n_groups = values['NUM_GROUPS']
    cores_per_tile = values['NUM_CORES_PER_TILE']
    n_subgroups = values['NUM_SUB_GROUPS_PER_GROUP']
    if n_cores % cores_per_tile:
        raise ValueError(
            'NUM_CORES must be divisible by NUM_CORES_PER_TILE')
    n_tiles = n_cores // cores_per_tile
    if n_tiles % n_groups:
        raise ValueError('The number of tiles must be divisible by NUM_GROUPS')
    tiles_per_group = n_tiles // n_groups
    if tiles_per_group % n_subgroups:
        raise ValueError(
            'The number of tiles per group must be divisible by '
            'NUM_SUB_GROUPS_PER_GROUP')

    # Keep topology.env keys and add lowercase derived values for consumers.
    topology.update(values)
    banks_per_tile = cores_per_tile * values['BANKING_FACTOR']

    topology.update({
        'n_cores': n_cores,
        'n_groups': n_groups,
        'cores_per_tile': cores_per_tile,
        'cores_per_group': n_cores // n_groups,
        'n_tiles': n_tiles,
        'tiles_per_group': tiles_per_group,
        'n_subgroups_per_group': n_subgroups,
        'remote_group_latency_cycles':
            values['REMOTE_GROUP_LATENCY_CYCLES'],
        'tiles_per_subgroup': tiles_per_group // n_subgroups,
        'banks_per_tile': banks_per_tile,
        'seq_mem_size_per_tile': (
            cores_per_tile * values['SEQ_MEM_SIZE']),
        'interleave_stride': 4 * banks_per_tile,  # Four bytes per TCDM word.
        'tcdm_size': (
            banks_per_tile * values['L1_BANK_SIZE'] * n_tiles),
    })
    return topology


def load_topology(path) -> dict:
    """Read a topology.env file; every TOPOLOGY_KEYS entry is required."""
    path = Path(path)
    if not path.is_file():
        raise ValueError(
            f'Missing topology file: {path}\n'
            'Every `make benchmark` run writes it; for foreign data '
            'create it by hand (see the README).')
    values = {}
    for line in path.read_text().splitlines():
        key, sep, value = line.strip().partition('=')
        if sep and key and not key.startswith('#'):
            values[key.strip()] = value.strip()
    missing = [key for key in TOPOLOGY_KEYS if key not in values]
    if missing:
        raise ValueError(f'{path} is missing: {", ".join(missing)}')
    topology = {key: int(values[key]) for key in TOPOLOGY_KEYS}
    topology.update({
        key: values.get(key, default)
        for key, default in OPTIONAL_TOPOLOGY_DEFAULTS.items()
    })
    topology['config'] = values.get('CONFIG', '')
    return derive_topology(topology)


def describe(topology: dict) -> str:
    config = topology.get('config')
    parts = [f'config={config}'] if config else []
    keys = (*TOPOLOGY_KEYS, *OPTIONAL_TOPOLOGY_DEFAULTS)
    parts += [f'{key.lower()}={topology[key]}' for key in keys]
    return ', '.join(parts)
