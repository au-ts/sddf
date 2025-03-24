# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause
import argparse
from typing import List
from dataclasses import dataclass
from sdfgen import SystemDescription, Sddf, DeviceTree

ProtectionDomain = SystemDescription.ProtectionDomain
MemoryRegion = SystemDescription.MemoryRegion
Map = SystemDescription.Map
Irq = SystemDescription.Irq


@dataclass
class Board:
    name: str
    arch: SystemDescription.Arch
    paddr_top: int
    can: str


BOARDS: List[Board] = [
    Board(
        name="imx8mp_evk",
        arch=SystemDescription.Arch.AARCH64,
        paddr_top=0xa0000000,
        can="soc@0/bus@30800000/spba-bus@30800000/can@308c0000" # This is from the symbol table under 'flexcan1'
    ),
]


def generate(sdf_file: str, output_dir: str, dtb: DeviceTree):
    can_driver = ProtectionDomain("can_driver", "can_driver.elf", priority=254)
    client = ProtectionDomain("client", "client.elf", priority=1)
    
    # reg = <0x308c0000 0x10000>;
    can_mr = MemoryRegion("reg", 0x10000, paddr=0x308c0000)

    # clocks
    clock_mr = MemoryRegion("clock", 0x10000, paddr=0x30380000);
    can_driver.add_map(Map(clock_mr, 0x2000000, "rw", cached=False));
    sdf.add_mr(clock_mr)
    
    # interrupts = <0x00 0x8e 0x04>;
    # => 0x8e = 142, then add 32 = 174 
    # Note this defaults to level triggered
    can_irq = Irq(174)

    can_driver.add_irq(can_irq)
    can_driver.add_map(Map(can_mr, 0x1000000, "rw", cached=False)) # We set the vaddr for the device here - this is fixed and should map to the physical address of the device
    
    sdf.add_mr(can_mr)

    pds = [
        can_driver,
        client
    ]
    for pd in pds:
        sdf.add_pd(pd)

    with open(f"{output_dir}/{sdf_file}", "w+") as f:
        f.write(sdf.render())


if __name__ == '__main__':
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
