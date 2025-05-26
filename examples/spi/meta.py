# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause
import argparse
from typing import List
from dataclasses import dataclass
from sdfgen import SystemDescription, Sddf, DeviceTree
from importlib.metadata import version

assert version('sdfgen').split(".")[1] == "24", "Unexpected sdfgen version"

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


BOARDS: List[Board] = [
    Board(
        name="cheshire",
        arch=SystemDescription.Arch.AARCH64,
        paddr_top=0xa_000_000,
    ),
]


def generate(sdf_file: str, output_dir: str, dtb: DeviceTree):
    _ = """spi_driver = ProtectionDomain("spi_driver", "spi_driver.elf", priority=254)
    spi_driver.add_irq(Irq(17, id=0))
    spi_driver.add_irq(Irq(18, id=1))
    spi_mr = MemoryRegion("spi_meta", 0x1000, paddr=0x3004000)
    spi_driver.add_map(Map(spi_mr, 0x10_000_000, perms="rw", cached=False))
    """
    
    client_virt_meta = MemoryRegion("client_virt_meta", 0x1000)
    data = MemoryRegion("data", 0x1000)
    
    spi_client = ProtectionDomain("spi_client", "client.elf") 
    spi_client.add_map(Map(client_virt_meta, 0x10_000_000, perms="rw"))
    spi_client.add_map(Map(data, 0x10_001_000, perms="rw"))
    
    spi_virt = ProtectionDomain("spi_virt", "spi_virt.elf", priority=253)
    spi_virt.add_map(Map(client_virt_meta, 0x10_000_000, perms="rw"))
    spi_virt.add_map(Map(data, 0x10_001_000, perms="rw"))
 
    client_virt_ch = Channel(spi_client, spi_virt, pp_a=True, b_id=1)

    pds = [
        spi_client,
        spi_virt
        #spi_driver,
    ]
    for pd in pds:
        sdf.add_pd(pd)
    sdf.add_mr(client_virt_meta)
    sdf.add_mr(data)
    sdf.add_channel(client_virt_ch)

    with open(f"{output_dir}/{sdf_file}", "w+") as f:
        f.write(sdf.render())


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    # parser.add_argument("--dtb", required=True)
    parser.add_argument("--sddf", required=True)
    parser.add_argument("--board", required=True, choices=[b.name for b in BOARDS])
    parser.add_argument("--output", required=True)
    parser.add_argument("--sdf", required=True)

    args = parser.parse_args()

    board = next(filter(lambda b: b.name == args.board, BOARDS))

    sdf = SystemDescription(board.arch, board.paddr_top)
    sddf = Sddf(args.sddf)

    # with open(args.dtb, "rb") as f:
    #    dtb = DeviceTree(f.read())

    generate(args.sdf, args.output, None)
