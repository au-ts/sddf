# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause
import os
import sys
import argparse
from sdfgen import SystemDescription, Sddf, DeviceTree
import importlib

sys.path.append(
    os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../tools/meta")
)

# Use importlib to dynamically load. Using `from` import below other code is bad style.
board_module = importlib.import_module("board")
BOARDS = board_module.BOARDS

ProtectionDomain = SystemDescription.ProtectionDomain
MemoryRegion = SystemDescription.MemoryRegion
Map = SystemDescription.Map


def generate(sdf_file: str, output_dir: str, dtb: DeviceTree):
    sound_driver = ProtectionDomain("sound_driver", "sound_driver.elf", priority=253)
    client = ProtectionDomain("client", "client.elf", priority=1)

    device_mr = MemoryRegion(sdf, "virtio-sound-device", 0x1000, paddr=0xa003000)
    sdf.add_mr(device_mr)
    sound_driver.add_map(Map(device_mr, 0x20_003_000, "rw", cached=False))

    virtio_queues = MemoryRegion(sdf, "virtio_queues", 0x400_000, paddr=0x5_0000_000)
    sdf.add_mr(virtio_queues)
    sound_driver.add_map(Map(virtio_queues, 0x30_000_000, "rw", cached=False))

    virtio_data = MemoryRegion(sdf, "virtio_data", 0x400_000, paddr=0x5_5000_000)
    sdf.add_mr(virtio_data)
    sound_driver.add_map(Map(virtio_data, 0x40_000_000, "rw", cached=False))

    sound_driver.add_irq(SystemDescription.IrqConventional(79, trigger=SystemDescription.IrqConventional.Trigger.EDGE))

    pds = [sound_driver, client]
    for pd in pds:
        sdf.add_pd(pd)

    with open(f"{output_dir}/{sdf_file}", "w+") as f:
        f.write(sdf.render())


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--dtb", required=False)
    parser.add_argument("--sddf", required=True)
    parser.add_argument("--board", required=True, choices=[b.name for b in BOARDS])
    parser.add_argument("--output", required=True)
    parser.add_argument("--sdf", required=True)

    args = parser.parse_args()

    board = next(filter(lambda b: b.name == args.board, BOARDS))

    sdf = SystemDescription(board.arch, board.paddr_top)
    sddf = Sddf(args.sddf)

    dtb = None
    if board.arch != SystemDescription.Arch.X86_64:
        with open(args.dtb, "rb") as f:
            dtb = DeviceTree(f.read())

    generate(args.sdf, args.output, dtb)
