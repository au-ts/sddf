# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause
import sys, os
import argparse
from typing import List
from dataclasses import dataclass
from acacia import System, ProtectionDomain, MemoryRegion, Channel, DeviceTreeBlob
from acacia.arch import x86_64

sys.path.append(os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../"))
from acacia_sddf import sDDFSerial, BOARDS


def generate(sdf_file: str, output_dir: str):
    client0 = ProtectionDomain("client0", "client0.elf", sdf, priority=1)
    client1 = ProtectionDomain("client1", "client1.elf", sdf, priority=1)

    serial = sDDFSerial(
        board.serial.compatible,
        board.serial.node_path,
        sdf,
        driver_prio=200,
        virt_tx_prio=199,
        allow_rx=True,
        enable_color=True,
        baud_rate=board.baud_rate if board.baud_rate else 115200,
    )

    for pd in [client0, client1]:
        serial.add_client(pd)

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
