# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause
import sys, os
import argparse
from typing import List
from dataclasses import dataclass
from sdfgen import SystemDescription, Sddf, DeviceTree
from importlib.metadata import version

sys.path.append(
    os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../tools/meta")
)
from board import BOARDS

assert version("sdfgen").split(".")[1] == "27", "Unexpected sdfgen version"

ProtectionDomain = SystemDescription.ProtectionDomain


def generate(sdf_file: str, output_dir: str, dtb: DeviceTree):
    serial_driver = ProtectionDomain("serial_driver", "serial_driver.elf", priority=200)
    serial_virt_tx = ProtectionDomain(
        "serial_virt_tx", "serial_virt_tx.elf", priority=199
    )
    serial_virt_rx = ProtectionDomain(
        "serial_virt_rx", "serial_virt_rx.elf", priority=199
    )

    if board.arch == SystemDescription.Arch.X86_64:
        serial_port = SystemDescription.IoPort(
            SystemDescription.Arch.X86_64, 0x3F8, 8, 0
        )
        serial_driver.add_ioport(serial_port)

        # The serial device does not located on PCIe and the interrupts are
        # conventionally configured by BIOS. The IRQ number can be read from
        # Linux or APCI tables.
        serial_irq = SystemDescription.IrqIoapic(board.arch, 0, 4, 0, id=1)
        serial_driver.add_irq(serial_irq)

    client0 = ProtectionDomain("client0", "client0.elf", priority=1)
    client1 = ProtectionDomain("client1", "client1.elf", priority=1)

    serial_node = None
    if dtb is not None:
        serial_node = dtb.node(board.serial)
        assert serial_node is not None

    serial_system = Sddf.Serial(
        sdf, serial_node, serial_driver, serial_virt_tx, virt_rx=serial_virt_rx
    )
    serial_system.add_client(client0)
    serial_system.add_client(client1)

    pds = [
        serial_driver,
        serial_virt_tx,
        serial_virt_rx,
        client0,
        client1,
    ]
    for pd in pds:
        sdf.add_pd(pd)

    assert serial_system.connect()
    assert serial_system.serialise_config(output_dir)

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
