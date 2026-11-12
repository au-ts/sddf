# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause
import argparse
import os
import sys
from pathlib import Path

from acacia import DeviceTreeBlob, ProtectionDomain, System
from acacia.arch import x86_64

sys.path.append(os.path.join(os.path.dirname(os.path.abspath(__file__)), "../.."))
from acacia_sddf import BOARDS, sDDFTimer


def generate(sdf_file: str, output_dir: str):
    client = ProtectionDomain(sdf, "client", "client.elf", priority=1)

    timer = sDDFTimer(sdf, board.timer.compatible, board.timer.node_path)
    timer.add_client(client)

    if args.multikernel:
        local_client = ProtectionDomain(sdf, "local_client", "client.elf", priority=1)
        timer.add_client(local_client)
        from acacia import Multikernel
        sdf.resolve_subsystems()
        multi_k = Multikernel(sdf, args.multikernel)
        multi_k.prepare(Path(output_dir) / "multikernel")

    sdf.make_config_structs()
    out_file = f"{output_dir}/{sdf_file}"
    if args.multikernel:
        multi_k.write(Path(output_dir) / "multikernel")
    else:
        sdf.write_xml_file(out_file)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--dtb", required=False)
    parser.add_argument("--sddf", required=True)
    parser.add_argument("--board", required=True, choices=[b.name for b in BOARDS])
    parser.add_argument("--output", required=True)
    parser.add_argument("--sdf", required=True)
    parser.add_argument("--multikernel", type=Path, help="Parition configuration JSON")

    args = parser.parse_args()

    board = next(filter(lambda b: b.name == args.board, BOARDS))

    if board.arch != x86_64:
        dtb = DeviceTreeBlob(args.dtb)
    else:
        dtb = None
    sdf = System(board.arch, board.paddr_top, dtb)

    generate(args.sdf, args.output)
