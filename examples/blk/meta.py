# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause
import os, sys
import argparse
from typing import List, Optional
from dataclasses import dataclass
from acacia import (
    System,
    ProtectionDomain,
    MemoryRegion,
    Channel,
    DeviceTreeBlob,
    Map,
    IOPort,
    IrqIoapic,
)
from acacia.arch import aarch64, x86_64, riscv64

sys.path.append(os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../"))
from acacia_sddf import BOARDS, sDDFBlk, sDDFSerial, sDDFTimer


def generate(
    sdf_file: str,
    output_dir: str,
    dtb: Optional[DeviceTreeBlob],
    need_timer: bool,
    nvme: bool,  # hack to select NVMe or Virtio
):
    client = ProtectionDomain(sdf, "client", "client.elf", priority=1)
    serial = sDDFSerial(
        sdf,
        board.serial.compatible,
        board.serial.node_path,
        driver_prio=200,
        virt_tx_prio=199,
        allow_rx=False,
        enable_color=False,
        baud_rate=board.baud_rate if board.baud_rate else 115200,
    )
    serial.add_client(client)

    blk = sDDFBlk(sdf, board.blk.compatible, board.blk.node_path, 200, 199)
    partition = int(args.partition) if args.partition else board.partition
    blk.add_client(client, partition)

    blk_driver = blk.driver
    blk_virt = blk.virt

    if need_timer:
        timer = sDDFTimer(sdf, board.timer.compatible, board.timer.node_path)
        timer.add_client(blk_driver)

    if nvme:
        # Queue descriptors accessed via DMA so we map these regions as uncached.
        if board.arch == riscv64:
            dma_regions = [
                ("nvme_admin_sq", 0x9EDF0000, 0x20100000, 0x1000),
                ("nvme_admin_cq", 0x9EDF1000, 0x20101000, 0x1000),
                ("nvme_io_sq", 0x9EDF2000, 0x20102000, 0x1000),
                ("nvme_io_cq", 0x9EDF3000, 0x20103000, 0x1000),
                ("nvme_identify", 0x9EDF4000, 0x20104000, 0x2000),
                ("nvme_prp_list", 0x9F800000, 0x20200000, 0x80000),
            ]
        else:
            dma_regions = [
                ("nvme_admin_sq", 0x5EDF0000, 0x20100000, 0x1000),
                ("nvme_admin_cq", 0x5EDF1000, 0x20101000, 0x1000),
                ("nvme_io_sq", 0x5EDF2000, 0x20102000, 0x1000),
                ("nvme_io_cq", 0x5EDF3000, 0x20103000, 0x1000),
                ("nvme_identify", 0x5EDF4000, 0x20104000, 0x2000),
                ("nvme_prp_list", 0x5F800000, 0x20200000, 0x80000),
            ]
        for name, paddr, vaddr, size in dma_regions:
            mr = MemoryRegion(sdf, name, size, paddr=paddr, cached=False)
            blk_driver.add_map(Map(mr, vaddr, "rw"))

        if board.arch == x86_64:
            # BAR0: MMIO (always uncached)
            nvme_bar0_mr = MemoryRegion(
                sdf, "nvme_bar0", 0x4000, paddr=0xFEBD4000, cached=False
            )

            # IRQ
            nvme_irq = IrqIoapic(ioapic_id=0, pin=10, vector=1, id=17)

        elif board.arch == aarch64:
            # BAR0: MMIO (always uncached)
            nvme_bar0_mr = MemoryRegion(
                sdf, "nvme_bar0", 0x4000, paddr=0x10000000, cached=False
            )

            # ECAM config page: MMIO (always uncached)
            nvme_ecam_mr = MemoryRegion(
                sdf, "nvme_ecam", 0x1000, paddr=0x4010020000, cached=False
            )
            blk_driver.add_map(Map(nvme_ecam_mr, 0x20300000, "rw"))

            # IRQ: slot 4 INT_A -> PCI irq line (1+4)%4 = 1 -> SPI 3 -> GIC IRQ 35
            nvme_irq = IrqConventional(irq=35, id=35)

        else:  # board.arch == riscv64:
            # BAR0: MMIO (always uncached)
            nvme_bar0_mr = MemoryRegion(
                sdf, "nvme_bar0", 0x4000, paddr=0x40000000, cached=False
            )

            # ECAM config page: MMIO (always uncached)
            nvme_ecam_mr = MemoryRegion(
                sdf, "nvme_ecam", 0x1000, paddr=0x30020000, cached=False
            )
            blk_driver.add_map(Map(nvme_ecam_mr, 0x20300000, "rw"))

            # IRQ: slot 4 INT_A -> PCI irq line (0+4)%4 = 0 -> PLIC IRQ 0x20 = 32
            nvme_irq = IrqConventional(irq=32, id=32)

        blk_driver.add_map(Map(nvme_bar0_mr, 0x20000000, "rw"))

        blk_driver.add_irq(nvme_irq)

    if board.arch == x86_64:
        # IO ports
        pci_config_addr_port = IOPort(0xCF8, 4, 1)
        blk_driver.add_ioport(pci_config_addr_port)

        pci_config_data_port = IOPort(0xCFC, 4, 2)
        blk_driver.add_ioport(pci_config_data_port)

        # x86 virtio regions
        if not nvme:
            blk_requests_mr = MemoryRegion(
                sdf, "virtio_requests", 65536, paddr=0x5FDF0000
            )
            blk_requests_map = Map(blk_requests_mr, 0x20200000, "rw")
            blk_driver.add_map(blk_requests_map)

            blk_virtio_metadata_mr = MemoryRegion(
                sdf, "virtio_metadata", 65536, paddr=0x5FFF0000
            )
            blk_virtio_metadata_map = Map(blk_virtio_metadata_mr, 0x20210000, "rw")
            blk_driver.add_map(blk_virtio_metadata_map)

            virtio_blk_regs = MemoryRegion(
                sdf, "virtio_blk_regs", 0x4000, paddr=0xFE000000, cached=False
            )
            virtio_blk_regs_map = Map(virtio_blk_regs, 0x6000_0000, "rw")
            blk_driver.add_map(virtio_blk_regs_map)

            virtio_blk_irq = IrqIoapic(ioapic_id=0, pin=11, vector=1, id=17)
            blk_driver.add_irq(virtio_blk_irq)
    out_file = f"{output_dir}/{sdf_file}"
    sdf.make_config_structs()
    print(f"Saving to {out_file}")
    sdf.write_xml_file(out_file)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--dtb", required=False)
    parser.add_argument("--board", required=True, choices=[b.name for b in BOARDS])
    parser.add_argument("--output", required=True)
    parser.add_argument("--sdf", required=True)
    parser.add_argument("--need_timer", action="store_true", default=False)
    parser.add_argument("--nvme", action="store_true", default=False)
    parser.add_argument("--partition")

    args = parser.parse_args()

    board = next(filter(lambda b: b.name == args.board, BOARDS))

    dtb = DeviceTreeBlob(args.dtb) if args.dtb else None
    sdf = System(board.arch, board.paddr_top, dtb)
    generate(args.sdf, args.output, dtb, args.need_timer, args.nvme)
