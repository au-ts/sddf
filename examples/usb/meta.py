# Copyright 2026, UNSW
# SPDX-License-Identifier: BSD-2-Clause
import os, sys
import argparse
from typing import List, Optional
from dataclasses import dataclass
from sdfgen import SystemDescription, Sddf, DeviceTree
from importlib.metadata import version

sys.path.append(
    os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../tools/meta")
)
from board import BOARDS

assert version("sdfgen").split(".")[1] == "28", "Unexpected sdfgen version"

def generate(
    sdf_file: str,
    output_dir: str,
    dtb: Optional[DeviceTree],
):
    # TODO: dtb for ARM, only handling x86 for now

    usb_hcd = SystemDescription.ProtectionDomain(
        "usb_hcd", "usb_hcd.elf", priority=200, stack_size=0x2000
    )

    client = SystemDescription.ProtectionDomain(
        "client", "client.elf", priority=1
    )

    # TODO: Sddf.Usb - add somewhere?

    if board.arch == SystemDescription.Arch.X86_64:
        # xHCI MMIO space (paddr hardcoded from reading PCI BAR0) 
        xhci_bar0_mr = SystemDescription.MemoryRegion(
            sdf, "xhci_bar0", 0x4000, paddr=0xFEBD4000
        )
        sdf.add_mr(xhci_bar0_mr)
        xhci_bar0_map = SystemDescription.Map(
            xhci_bar0_mr, 0x20000000, "rw", cached=False
        )
        usb_hcd.add_map(xhci_bar0_map)
    
        # TODO: xHCI DMA memory for rings, TRBs, etc
        xhci_dma = SystemDescription.MemoryRegion(
            sdf, "ehci_dma", 0x40000, paddr=0x7000_0000
        )
        sdf.add_mr(xhci_dma)

        xhci_dma_map = SystemDescription.Map(
            xhci_dma, 0x7000_0000, "rw", cached=False
        ) # identity mapping
        usb_hcd.add_map(xhci_dma_map)
 
        # TODO: configure PCI interrupts and map it here SystemDescription.IrqIoapic?

        # hardcoded: should be found by PCI enumeration.
        xhci_irq = SystemDescription.IrqIoapic(ioapic_id=0, pin=10, vector=1, id=18)
        usb_hcd.add_irq(xhci_irq)

        # PCI IO ports for talking over PCI and setting up BAR etc
        pci_config_addr_port = SystemDescription.IoPort(0xCF8, 4, 1)
        usb_hcd.add_ioport(pci_config_addr_port)

        pci_config_data_port = SystemDescription.IoPort(0xCFC, 4, 2)
        usb_hcd.add_ioport(pci_config_data_port)


    pds = [usb_hcd, client]

    for pd in pds:
        sdf.add_pd(pd)

    # TODO: .connect(), .serialise_config() methods if usb_hcd is in sddfgen

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