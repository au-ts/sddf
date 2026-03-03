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

assert version("sdfgen").split(".")[1] == "28", "Unexpected sdfgen version"

ProtectionDomain = SystemDescription.ProtectionDomain
MemoryRegion = SystemDescription.MemoryRegion
Map = SystemDescription.Map
Channel = SystemDescription.Channel
IrqConventional = SystemDescription.IrqConventional


def generate(sdf_file: str, output_dir: str, dtb: DeviceTree):

    timer_driver = ProtectionDomain("timer_driver", "timer_driver.elf", priority=250)
    client = ProtectionDomain("client", "client.elf", priority=1)
    pcie = ProtectionDomain("pcie", "pcie.elf", priority=240)
    usb = ProtectionDomain("usb", "usb.elf", priority=230)

    # maybe hard-coded paddr for qemu_virt_aarch64?
    pcie_config = MemoryRegion(sdf, "pcie_config", 0x100_0000, paddr=0x3eff_0000)

    ehci_regs = MemoryRegion(sdf, "ehci_regs", 0x1000, paddr=0x3800_0000)
    ehci_dma = MemoryRegion(sdf, "ehci_dma", 0x10000, paddr=0x7000_0000)

    pcie_usb_ch = Channel(pcie, usb, a_id=3, b_id=3)

    pcie.add_map(Map(pcie_config, 0x20_000_000, "rw", cached=False))
    usb.add_map(Map(ehci_regs, 0x30_000_000, "rw", cached=False))
    usb.add_map(Map(ehci_dma, 0x7000_0000, "rw", cached=False)) # identity mapping

    sdf.add_channel(pcie_usb_ch)

    sdf.add_mr(pcie_config)
    sdf.add_mr(ehci_regs)
    sdf.add_mr(ehci_dma)

    # i think this is required?
    usb.add_irq(IrqConventional(0x49 + 32, id=1))

    # need timer for tinyUSB (this would need to be modified for x86 support)
    timer_system = Sddf.Timer(sdf, dtb.node(board.timer), timer_driver)
    timer_system.add_client(usb)


    pds = [
        client,
        pcie,
        usb,
        timer_driver
    ]

    for pd in pds:
        sdf.add_pd(pd)

    assert timer_system.connect()
    assert timer_system.serialise_config(output_dir)

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

