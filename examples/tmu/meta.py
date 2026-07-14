# Copyright 2026, UNSW
# SPDX-License-Identifier: BSD-2-Clause
import os, sys
import argparse
from typing import List
from dataclasses import dataclass
from acacia import System, ProtectionDomain, MemoryRegion, Channel, DeviceTreeBlob, Map

sys.path.append(os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../"))
from acacia_sddf import BOARDS, sDDFSerial, sDDFTimer, sDDFTMU


def generate(sdf_file: str, output_dir: str, dtb: DeviceTreeBlob):
    client = ProtectionDomain(sdf, "client", "client.elf", priority=1)
    tmu = sDDFTMU(sdf, board.tmu.compatible, board.tmu.node_path, driver_prio=7)
    tmu.add_client(client)

    timer = sDDFTimer(sdf, board.timer.compatible, board.timer.node_path)
    timer.add_client(client)

    serial = sDDFSerial(
        sdf,
        board.serial.compatible,
        board.serial.node_path,
        driver_prio=201,
        virt_tx_prio=200,
        allow_rx=False,
        enable_color=False,
        baud_rate=board.baud_rate if board.baud_rate else 115200,
    )
    serial.add_client(client)

    out_file = f"{output_dir}/{sdf_file}"
    sdf.make_config_structs()
    print(f"Saving to {out_file}")
    sdf.write_xml_file(out_file)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--dtb", required=True)
    parser.add_argument("--sddf", required=True)
    parser.add_argument("--board", required=True, choices=[b.name for b in BOARDS])
    parser.add_argument("--output", required=True)
    parser.add_argument("--sdf", required=True)

    args = parser.parse_args()

    board = next(filter(lambda b: b.name == args.board, BOARDS))

    dtb = DeviceTreeBlob(args.dtb)
    sdf = System(board.arch, board.paddr_top, dtb)

    generate(args.sdf, args.output, dtb)
