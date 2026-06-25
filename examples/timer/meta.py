# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause
import os
import sys
import argparse
import importlib
from acacia import System, ProtectionDomain, MemoryRegion, Channel, DeviceTreeBlob
from acacia.arch import x86_64

# Use importlib to dynamically load. Using `from` import below other code is bad style.
# board_module = importlib.import_module("board")
sys.path.append(
    os.path.join(os.path.dirname(os.path.abspath(__file__)), "../..")
)
from acacia_sddf import BOARDS, sDDFTimer

def generate(sdf_file: str, output_dir: str):
    client = ProtectionDomain("client", "client.elf", priority=1)


    timer = sDDFTimer(board.timer.compatible, board.timer.node_path, sdf)
    timer.add_client(client)
    sdf.add_subsystem(timer)
    sdf.add_pd(client)

    # Add HPET if x86
    if board.arch == x86_64:
        timer.add_x86_hpet(sdf)

    sdf.make_config_structs()
    out_file = f"{output_dir}/{sdf_file}"
    print(f"Saving to {out_file}")
    sdf.write_xml_file(out_file)

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--dtb", required=False)
    parser.add_argument("--sddf", required=True)
    parser.add_argument("--board", required=True, choices=[b.name for b in BOARDS])
    parser.add_argument("--output", required=True)
    parser.add_argument("--sdf", required=True)

    args = parser.parse_args()

    board = next(filter(lambda b: b.name == args.board, BOARDS))

    if board.arch != x86_64:
        dtb = DeviceTreeBlob(args.dtb)
    else:
        dtb = None
    sdf = System(board.arch, board.paddr_top, dtb)

    generate(args.sdf, args.output)
