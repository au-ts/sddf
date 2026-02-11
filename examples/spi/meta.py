# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause
import argparse
from typing import List
from dataclasses import dataclass
from sdfgen import SystemDescription, Sddf, DeviceTree
from importlib.metadata import version

assert version("sdfgen").split(".")[1] == "28", "Unexpected sdfgen version"

ProtectionDomain = SystemDescription.ProtectionDomain
Irq = SystemDescription.Irq
Map = SystemDescription.Map
MemoryRegion = SystemDescription.MemoryRegion
Channel = SystemDescription.Channel


@dataclass
class Board:
    name: str
    arch: SystemDescription.Arch
    paddr_top: int
    spi: str


BOARDS: List[Board] = [
    Board(
        name="cheshire",
        arch=SystemDescription.Arch.RISCV64,
        paddr_top=0xC0000000,
        spi="soc/spi@3004000",
    ),
]


def generate(sdf_file: str, output_dir: str, dtb: DeviceTree):
    spi_driver = ProtectionDomain(
        "spi_driver", "spi_driver.elf", priority=3, stack_size=16384
    )
    spi_virt = ProtectionDomain("spi_virt", "spi_virt.elf", priority=2)
    spi_client = ProtectionDomain("spi_client", "client.elf", priority=1)

    spi_node = dtb.node(board.spi)

    spi_system = Sddf.Spi(sdf, spi_node, spi_driver, spi_virt)
    spi_system.add_client(spi_client, cs=2, freq_div=0x7F, queue_capacity=16)

    pds = [
        spi_client,
        spi_virt,
        spi_driver,
    ]
    for pd in pds:
        sdf.add_pd(pd)

    assert spi_system.connect()
    assert spi_system.serialise_config(output_dir)

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
