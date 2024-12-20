#!/usr/bin/env python3
# Copyright 2024 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import pandas as pd
import numpy as np
import matplotlib.pyplot as plt
import matplotlib.colors as mcolors
import ast


scale_factor = 10


def visualize_mesh_noc_congestion_optimized(
    file_path, output_png, output_pdf, req_rsp, NumX=4, NumY=4
):
    # Load and preprocess the data
    with open(file_path, "r") as file:
        raw_content = file.readlines()

    parsed_data = []
    for line in raw_content:
        line = line.strip()
        if line.startswith("{") and not line.endswith("}"):
            line += "}"  # Append a closing brace if missing
        try:
            entry = ast.literal_eval(line)  # Parse JSON-like entries
            parsed_data.append(entry)
        except Exception:
            continue

    df = pd.DataFrame(parsed_data)
    if df.empty:
        print("Error: No valid data found in the file.")
        return

    # Filter data for REQ_RSP == 0 (request NoC)
    req_noc_data = df[df["REQ_RSP"] == req_rsp]

    # Calculate congestion for inbound and outbound links (1 - handshake/valid)
    max_hsk = req_noc_data["out_hsk_cyc_num"].max()
    # req_noc_data['in_congestion'] =
    # (req_noc_data['in_hsk_cyc_num'] / (max_hsk))
    req_noc_data["out_congestion"] = req_noc_data["out_hsk_cyc_num"] / (
        max_hsk
    )

    # Normalize congestion for color mapping
    # (0: least congested, 1: most congested)
    # req_noc_data['in_congestion_norm'] =
    # np.clip(req_noc_data['in_congestion'], 0, 1)
    req_noc_data["out_congestion_norm"] = np.clip(
        req_noc_data["out_congestion"], 0, 1
    )
    print(req_noc_data)

    # Define a color map for congestion visualization (green -> yellow -> red)
    congestion_cmap = plt.cm.get_cmap("RdYlGn_r")

    # Helper function to get router coordinates from group ID
    def get_router_coords(group_id):
        x = group_id // NumX  # Column index
        y = group_id % NumY  # Row index
        # Reverse Y-axis for visualization
        # return x * scale_factor, ((NumY-1) - y) * scale_factor
        return (
            x * scale_factor,
            y * scale_factor,
        )  # Reverse Y-axis for visualization

    # Draw the mesh NoC with congestion-based links
    plt.figure(figsize=(10, 8.4))
    for _, row in req_noc_data.iterrows():
        src_coords = get_router_coords(row["GROUP"])

        # print(row)

        # Skip invalid links based on edge and corner conditions
        if (
            row["DIR"] == 0 and src_coords[1] == 3 * scale_factor
        ):  # North link for top row routers
            continue
        if (
            row["DIR"] == 1 and src_coords[0] == 3 * scale_factor
        ):  # East link for rightmost column routers
            continue
        if (
            row["DIR"] == 2 and src_coords[1] == 0 * scale_factor
        ):  # South link for bottom row routers
            continue
        if (
            row["DIR"] == 3 and src_coords[0] == 0 * scale_factor
        ):  # West link for leftmost column routers
            continue

        # Determine destination coordinates
        if row["DIR"] == 0:  # North
            dest_coords = (src_coords[0], src_coords[1] + 1 * scale_factor)
        elif row["DIR"] == 1:  # East
            dest_coords = (src_coords[0] + 1 * scale_factor, src_coords[1])
        elif row["DIR"] == 2:  # South
            dest_coords = (src_coords[0], src_coords[1] - 1 * scale_factor)
        elif row["DIR"] == 3:  # West
            dest_coords = (src_coords[0] - 1 * scale_factor, src_coords[1])
        else:
            continue

        # Determine the congestion level and color
        # congestion_level =
        # (row['in_congestion_norm'] + row['out_congestion_norm']) / 2
        # we only need outbound, because it is the inbound of its pair routers
        congestion_level = row["out_congestion_norm"]
        link_color = congestion_cmap(congestion_level)

        # Offset
        granularity = 0.05
        offset_x = 0
        offset_y = 0
        if row["DIR"] == 1 or row["DIR"] == 3:
            offset_y = (
                row["TILE"] * granularity * 2 + row["PORT"] * granularity
            )
        else:
            offset_x = (
                row["TILE"] * granularity * 2 + row["PORT"] * granularity
            )

        if row["DIR"] == 1:
            offset_y += granularity * 20
        elif row["DIR"] == 3:
            offset_y -= granularity * 20
        elif row["DIR"] == 0:
            offset_x += granularity * 20
        elif row["DIR"] == 2:
            offset_x -= granularity * 20
        else:
            continue

        # Draw the link
        # plt.plot(
        #     [src_coords[0] + offset_x, dest_coords[0] + offset_x],
        #     [src_coords[1] + offset_y, dest_coords[1] + offset_y],
        #     color=link_color,
        #     linewidth=1,
        #     alpha=1,
        # )
        plt.plot(
            [src_coords[0] + offset_x, dest_coords[0] + offset_x],
            [src_coords[1] + offset_y, dest_coords[1] + offset_y],
            color=link_color,
            linewidth=1,
            alpha=1,
        )

    # Add routers as nodes
    offset_dir = 0.8
    for group_id in range(NumX * NumY):  # 4x4 mesh
        x, y = get_router_coords(group_id)
        plt.scatter(
            x + offset_dir,
            y + offset_dir,
            color="orange",
            s=1200,
            edgecolor="black",
            zorder=11,
        )
        plt.text(
            x + offset_dir,
            y + offset_dir,
            f"R{group_id}",
            ha="center",
            va="center",
            fontsize=15,
            zorder=12,
        )

        for direction in range(4):  # 4 router directions
            offset_x = 0
            offset_y = 0
            x_2 = x
            y_2 = y
            offset_arrow = 0.5

            # Skip invalid links based on edge and corner conditions
            if (
                y == (NumY - 1) * scale_factor and direction == 0
            ):  # North link for top row routers
                continue
            if (
                x == (NumX - 1) * scale_factor and direction == 1
            ):  # East link for rightmost column routers
                continue
            if y == 0 and direction == 2:  # South link for bottom row routers
                continue
            if (
                x == 0 and direction == 3
            ):  # West link for leftmost column routers
                continue

            if direction == 0:  # North link for top row routers
                offset_x = 0
                offset_y = scale_factor / 2
                x_2 = x + offset_arrow + offset_dir
            elif direction == 1:  # East link for rightmost column routers
                offset_x = scale_factor / 2
                offset_y = 0
                y_2 = y + offset_arrow + offset_dir
            elif direction == 2:  # South link for bottom row routers
                offset_x = 0
                offset_y = -scale_factor / 2
                x_2 = x - offset_arrow + offset_dir
            elif direction == 3:  # West link for leftmost column routers
                offset_x = -scale_factor / 2
                offset_y = 0
                y_2 = y - offset_arrow + offset_dir
            else:
                continue

            plt.arrow(
                x_2,
                y_2,
                offset_x,
                offset_y,
                head_width=1,
                head_length=1,
                color="black",
                length_includes_head=True,
                alpha=0.8,
                width=0.02,
                zorder=10,
            )

    # Configure plot
    if req_rsp:
        plt.title(
            "4x4 Mesh NoC Bandwidth Visualization (resp network)", fontsize=16
        )
    else:
        plt.title(
            "4x4 Mesh NoC Bandwidth Visualization (req network)", fontsize=16
        )
    plt.axis("off")
    plt.colorbar(
        plt.cm.ScalarMappable(
            cmap=congestion_cmap, norm=mcolors.Normalize(vmin=0, vmax=1)
        ),
        label="Bandwidth Level",
    )

    # Save the output as PNG and PDF
    plt.savefig(output_png, format="png", bbox_inches="tight")
    plt.savefig(output_pdf, format="pdf", bbox_inches="tight")
    # plt.show()
    plt.clf()
    plt.close()


req_rsp = 0
for req_rsp in range(2):
    # Define file paths
    file_path = "spm_profiling/run_logs_f_1024/tests/router_level_profile_q_00038000.log"
    output_png = f"out/mesh_noc_bw_{req_rsp}.png"
    output_pdf = f"out/mesh_noc_bw_{req_rsp}.pdf"

    # Call the visualization function
    visualize_mesh_noc_congestion_optimized(
        file_path, output_png, output_pdf, req_rsp
    )

    # Define file paths
    file_path = "spm_profiling/run_logs_remap_f_1024/tests/router_level_profile_q_00038000.log"
    output_png = f"out/mesh_noc_remap_bw_{req_rsp}.png"
    output_pdf = f"out/mesh_noc_remap_bw_{req_rsp}.pdf"

    # Call the visualization function
    visualize_mesh_noc_congestion_optimized(
        file_path, output_png, output_pdf, req_rsp
    )
