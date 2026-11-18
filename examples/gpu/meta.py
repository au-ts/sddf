# Copyright 2026, UNSW
# SPDX-License-Identifier: BSD-2-Clause
import os
import sys
import argparse

from acacia import System, ProtectionDomain, DeviceTreeBlob

sys.path.append(os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../"))
from acacia_sddf import BOARDS, sDDFGpu, sDDFTimer


def generate(sdf_file: str, output_dir: str):
    if board.gpu.compatible is None:
        raise RuntimeError(f"Board {board.name} has no GPU device configured")

    client = ProtectionDomain(sdf, "client", "client.elf", priority=1)

    gpu = sDDFGpu(sdf, board.gpu.compatible, board.gpu.node_path, 254, 99)
    gpu.add_client(client)

    timer = sDDFTimer(sdf, board.timer.compatible, board.timer.node_path)
    timer.add_client(client)

    out_file = f"{output_dir}/{sdf_file}"
    sdf.make_config_structs()
    print(f"Saving to {out_file}")
    sdf.write_xml_file(out_file)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--dtb", required=True)
    parser.add_argument("--board", required=True, choices=[b.name for b in BOARDS])
    parser.add_argument("--output", required=True)
    parser.add_argument("--sdf", required=True)

    args = parser.parse_args()

    board = next(filter(lambda b: b.name == args.board, BOARDS))

    sdf = System(board.arch, board.paddr_top, DeviceTreeBlob(args.dtb))
    generate(args.sdf, args.output)
