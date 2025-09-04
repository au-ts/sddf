# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause
import argparse
from typing import List
from dataclasses import dataclass
from sdfgen import SystemDescription, Sddf, DeviceTree
from importlib.metadata import version

assert version("sdfgen").split(".")[1] == "24", "Unexpected sdfgen version"

ProtectionDomain = SystemDescription.ProtectionDomain
MemoryRegion = SystemDescription.MemoryRegion
Map = SystemDescription.Map

@dataclass
class Board:
    name: str
    arch: SystemDescription.Arch
    paddr_top: int
    timer: str


BOARDS: List[Board] = [
    Board(
        name="zcu102",
        arch=SystemDescription.Arch.AARCH64,
        paddr_top=0xA0000000,
        timer="axi/timer@ff140000",
    ),
]


def generate(sdf_file: str, output_dir: str, dtb: DeviceTree):
    timer_driver = ProtectionDomain("timer_driver", "timer_driver.elf", priority=254)

    client = ProtectionDomain("client", "dvfs.elf", priority=100)

    clk_mr = MemoryRegion("clk", 0x1000, paddr=0xFD1A0000)
    client.add_map(Map(clk_mr, 0xFD1A0000, "rw", cached=False))
    sdf.add_mr(clk_mr)

    timer_node = dtb.node(board.timer)
    assert timer_node is not None

    timer_system = Sddf.Timer(sdf, timer_node, timer_driver)
    timer_system.add_client(client)

    pds = [timer_driver, client]
    for pd in pds:
        sdf.add_pd(pd)

    assert timer_system.connect()
    assert timer_system.serialise_config(output_dir)

    with open(f"{output_dir}/{sdf_file}", "w+") as f:
        f.write(sdf.render())


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--dtb", required=True)
    parser.add_argument("--sddf", required=True)
    parser.add_argument("--board", required=True, choices=[b.name for b in BOARDS])
    parser.add_argument("--output", required=True)
    parser.add_argument("--sdf", required=True)

    args = parser.parse_args()

    board = next(filter(lambda b: b.name == args.board, BOARDS))

    sdf = SystemDescription(board.arch, board.paddr_top)
    sddf = Sddf(args.sddf)

    with open(args.dtb, "rb") as f:
        dtb = DeviceTree(f.read())

    generate(args.sdf, args.output, dtb)
