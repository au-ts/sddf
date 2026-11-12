# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause
import argparse
import os
import sys
from pathlib import Path

from acacia import DeviceTreeBlob, ProtectionDomain, System
from acacia.arch import x86_64

sys.path.append(os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../"))
from acacia_sddf import BOARDS, sDDFSerial


def generate(sdf_file: str, output_dir: str):
    client0 = ProtectionDomain(sdf, "client0", "client0.elf", priority=1)
    client1 = ProtectionDomain(sdf, "client1", "client1.elf", priority=1)

    serial = sDDFSerial(
        sdf,
        board.serial.compatible,
        board.serial.node_path,
        driver_prio=200,
        virt_tx_prio=199,
        allow_rx=True,
        enable_color=True,
        baud_rate=board.baud_rate if board.baud_rate else 115200,
    )

    for pd in [client0, client1]:
        serial.add_client(pd)

    if args.multikernel:
        from acacia import Multikernel

        sdf.resolve_subsystems()
        multi_k = Multikernel(sdf, args.multikernel)
        for client in (client0, client1):
            for mapping in client.maps:
                mapping.mr.physical = True
        multi_k.prepare(Path(output_dir) / "multikernel")

    sdf.make_config_structs()
    if args.multikernel:
        multi_k.write(Path(output_dir) / "multikernel")
    else:
        sdf.write_xml_file(f"{output_dir}/{sdf_file}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--dtb", required=False)
    parser.add_argument("--sddf", required=True)
    parser.add_argument("--board", required=True, choices=[b.name for b in BOARDS])
    parser.add_argument("--output", required=True)
    parser.add_argument("--sdf", required=True)
    parser.add_argument("--multikernel", type=Path, help="Partition configuration JSON")

    args = parser.parse_args()

    board = next(filter(lambda b: b.name == args.board, BOARDS))
    if board.arch != x86_64:
        dtb = DeviceTreeBlob(args.dtb)
    else:
        dtb = None
    sdf = System(board.arch, board.paddr_top, dtb)

    generate(args.sdf, args.output)
