# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause
import argparse
from typing import List
from dataclasses import dataclass
from sdfgen import SystemDescription, Sddf, DeviceTree
from importlib.metadata import version

assert version("sdfgen").split(".")[1] == "27", "Unexpected sdfgen version"

ProtectionDomain = SystemDescription.ProtectionDomain
MemoryRegion = SystemDescription.MemoryRegion
Map = SystemDescription.Map
Irq = SystemDescription.Irq


@dataclass
class Board:
    name: str
    arch: SystemDescription.Arch
    paddr_top: int


BOARDS: List[Board] = [
    Board(
        name="qemu_virt_aarch64",
        arch=SystemDescription.Arch.AARCH64,
        paddr_top=0xA_000_000,
    ),
]


def generate(sdf_file: str, output_dir: str, dtb: DeviceTree):
    input_driver = ProtectionDomain("input_driver", "input_driver.elf", priority=254, stack_size=0x2000)
    client = ProtectionDomain("client", "client.elf", priority=1)

    virtio_mr = MemoryRegion(sdf, "virtio", size=0x1000, paddr=0xa003000)
    virtio_queues = MemoryRegion(sdf, "virtio-queues", size=0x10000, paddr=0x70000000)
    virtio_events = MemoryRegion(sdf, "virtio-events", size=0x10000, paddr=0x80000000)
    sdf.add_mr(virtio_mr)
    sdf.add_mr(virtio_queues)
    sdf.add_mr(virtio_events)
    input_driver.add_map(Map(virtio_mr, 0xa003000, perms="rw", cached=False))
    input_driver.add_map(Map(virtio_queues, 0x70000000, perms="rw", cached=False))
    input_driver.add_map(Map(virtio_events, 0x80000000, perms="rw", cached=False))
    input_driver.add_irq(Irq(irq=79, trigger=Irq.Trigger.EDGE))


    pds = [input_driver, client]
    for pd in pds:
        sdf.add_pd(pd)

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
