# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause
import argparse
from typing import List
from dataclasses import dataclass
from sdfgen import SystemDescription, Sddf, DeviceTree

ProtectionDomain = SystemDescription.ProtectionDomain


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
        can="soc@0/bus@30000000/timer@302d0000" # TODO - Is this from the symbol table?
    ),
]


def generate(sdf_file: str, output_dir: str, dtb: DeviceTree):
    can_driver = ProtectionDomain("can_driver", "can_driver.elf", priority=254)
    client = ProtectionDomain("client", "client.elf", priority=1)

    can_node = dtb.node(board.can)
    assert can_node is not None

    can_system = Sddf.Timer(sdf, can_node, can_driver) # TODO - do I need to setup a new class for this?
    can_system.add_client(client)

    pds = [
        can_driver,
        client
    ]
    for pd in pds:
        sdf.add_pd(pd)

    assert can_system.connect()
    assert can_system.serialise_config(output_dir)

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
