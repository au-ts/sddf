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
Channel = SystemDescription.Channel


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
    keyboad_driver = ProtectionDomain("virtio_keyboard_driver", "virtio_keyboard_driver.elf", priority=254, stack_size=0x2000)
    mouse_driver = ProtectionDomain("virtio_mouse_driver", "virtio_mouse_driver.elf", priority=254, stack_size=0x2000)
    client = ProtectionDomain("client", "client.elf", priority=1)

    keyboard_inputs_mr = MemoryRegion(sdf, "keyboard-inputs", size=0x1000)
    mouse_inputs_mr = MemoryRegion(sdf, "mouse-inputs", size=0x1000)
    sdf.add_mr(keyboard_inputs_mr)
    sdf.add_mr(mouse_inputs_mr)

    virtio_mr = MemoryRegion(sdf, "virtio-device", size=0x1000, paddr=0xa003000)
    sdf.add_mr(virtio_mr)

    virtio_keyboard_queues = MemoryRegion(sdf, "virtio-keyboard-queues", size=0x10000, paddr=0x70000000)
    virtio_keyboard_events = MemoryRegion(sdf, "virtio-keyboard-events", size=0x10000, paddr=0x71000000)
    sdf.add_mr(virtio_keyboard_queues)
    sdf.add_mr(virtio_keyboard_events)
    keyboad_driver.add_map(Map(virtio_mr, 0xa003000, perms="rw", cached=False))
    keyboad_driver.add_map(Map(virtio_keyboard_queues, 0x70000000, perms="rw", cached=False))
    keyboad_driver.add_map(Map(virtio_keyboard_events, 0x71000000, perms="rw", cached=False))
    keyboad_driver.add_irq(Irq(irq=79, trigger=Irq.Trigger.EDGE))
    keyboad_driver.add_map(Map(keyboard_inputs_mr, 0x60000000, perms="rw", cached=False))

    virtio_mouse_queues = MemoryRegion(sdf, "virtio-mouse-queues", size=0x10000, paddr=0x80000000)
    virtio_mouse_events = MemoryRegion(sdf, "virtio-mouse-events", size=0x10000, paddr=0x81000000)
    sdf.add_mr(virtio_mouse_queues)
    sdf.add_mr(virtio_mouse_events)
    mouse_driver.add_map(Map(virtio_mr, 0xa003000, perms="rw", cached=False))
    mouse_driver.add_map(Map(virtio_mouse_queues, 0x80000000, perms="rw", cached=False))
    mouse_driver.add_map(Map(virtio_mouse_events, 0x81000000, perms="rw", cached=False))
    mouse_driver.add_irq(Irq(irq=78, trigger=Irq.Trigger.EDGE))
    mouse_driver.add_map(Map(mouse_inputs_mr, 0x60000000, perms="rw", cached=False))

    client.add_map(Map(mouse_inputs_mr, 0x10000000, perms="rw", cached=False))
    client.add_map(Map(keyboard_inputs_mr, 0x20000000, perms="rw", cached=False))

    sdf.add_channel(Channel(keyboad_driver, client, a_id=10, b_id=0))
    sdf.add_channel(Channel(mouse_driver, client, a_id=10, b_id=1))

    pds = [keyboad_driver, mouse_driver, client]
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
