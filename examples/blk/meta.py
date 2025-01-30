# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause
import argparse
from typing import List, Optional
from dataclasses import dataclass
from sdfgen import SystemDescription, Sddf, DeviceTree

ProtectionDomain = SystemDescription.ProtectionDomain


@dataclass
class Board:
    name: str
    arch: SystemDescription.Arch
    paddr_top: int
    blk: str
    # Default partition if the user has not specified one
    partition: int
    # Some block drivers need a timer driver as well, the example
    # itself does not need a timer driver.
    timer: Optional[str]


BOARDS: List[Board] = [
    Board(
        name="qemu_virt_aarch64",
        arch=SystemDescription.Arch.AARCH64,
        paddr_top=0x6_0000_000,
        partition=0,
        blk="virtio_mmio@a003e00",
        timer=None,
    ),
    Board(
        name="maaxboard",
        arch=SystemDescription.Arch.AARCH64,
        paddr_top=0x7_0000_000,
        partition=2,
        blk="soc@0/bus@30800000/mmc@30b40000",
        timer="soc@0/bus@30000000/timer@302d0000",
    ),
    Board(
        name="qemu_virt_riscv64",
        arch=SystemDescription.Arch.RISCV64,
        paddr_top=0xa_0000_000,
        partition=0,
        blk="soc/virtio_mmio@10008000",
        timer=None,
    ),
]


def generate(sdf_file: str, output_dir: str, dtb: DeviceTree):
    blk_driver = ProtectionDomain("blk_driver", "blk_driver.elf", priority=200)
    blk_virt = ProtectionDomain("blk_virt", "blk_virt.elf", priority=199, stack_size=0x2000)
    client = ProtectionDomain("client", "client.elf", priority=1)

    blk_node = dtb.node(board.blk)
    assert blk_node is not None
    if board.timer:
        timer_node = dtb.node(board.timer)
        assert timer_node is not None

        timer_driver = ProtectionDomain("timer_driver", "timer_driver.elf", priority=201)
        timer_system = sddf.Timer(sdf, timer_node, timer_driver)
        timer_system.add_client(blk_driver)

    blk_system = Sddf.Blk(sdf, blk_node, blk_driver, blk_virt)
    partition = int(args.partition) if args.partition else board.partition
    blk_system.add_client(client, partition=partition)

    pds = [
        blk_driver,
        blk_virt,
        client
    ]
    if board.timer:
        pds += [timer_driver]
    for pd in pds:
        sdf.add_pd(pd)

    assert blk_system.connect()
    assert blk_system.serialise_config(output_dir)
    if board.timer:
        assert timer_system.connect()
        assert timer_system.serialise_config(output_dir)

    with open(f"{output_dir}/{sdf_file}", "w+") as f:
        f.write(sdf.render())


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument("--dtb", required=True)
    parser.add_argument("--sddf", required=True)
    parser.add_argument("--board", required=True, choices=[b.name for b in BOARDS])
    parser.add_argument("--output", required=True)
    parser.add_argument("--sdf", required=True)
    parser.add_argument("--partition")

    args = parser.parse_args()

    board = next(filter(lambda b: b.name == args.board, BOARDS))

    sdf = SystemDescription(board.arch, board.paddr_top)
    sddf = Sddf(args.sddf)

    with open(args.dtb, "rb") as f:
        dtb = DeviceTree(f.read())

    generate(args.sdf, args.output, dtb)
