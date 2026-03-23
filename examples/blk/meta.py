# Copyright 2025, UNSW
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

ProtectionDomain = SystemDescription.ProtectionDomain


def generate(
    sdf_file: str,
    output_dir: str,
    dtb: Optional[DeviceTree],
    need_timer: bool,
    nvme: bool,  # hack to select NVMe or Virtio
):
    uart_node = None
    blk_node = None
    timer_node = None
    if dtb is not None:
        uart_node = dtb.node(board.serial)
        assert uart_node is not None
        blk_node = dtb.node(board.blk)
        assert blk_node is not None
        timer_node = dtb.node(board.timer)
        assert timer_node is not None

    serial_driver = ProtectionDomain("serial_driver", "serial_driver.elf", priority=200)
    # Increase the stack size as running with UBSAN uses more stack space than normal.
    serial_virt_tx = ProtectionDomain(
        "serial_virt_tx", "serial_virt_tx.elf", priority=199
    )

    serial_system = Sddf.Serial(
        sdf, uart_node, serial_driver, serial_virt_tx, enable_color=False
    )

    if board.arch == SystemDescription.Arch.X86_64:
        serial_port = SystemDescription.IoPort(0x3F8, 8, 0)
        serial_driver.add_ioport(serial_port)

    blk_driver = ProtectionDomain(
        "blk_driver", "blk_driver.elf", priority=200, stack_size=0x2000
    )
    blk_virt = ProtectionDomain(
        "blk_virt", "blk_virt.elf", priority=199, stack_size=0x2000
    )
    client = ProtectionDomain("client", "client.elf", priority=1)

    if need_timer:
        timer_driver = ProtectionDomain(
            "timer_driver", "timer_driver.elf", priority=201
        )
        timer_system = sddf.Timer(sdf, timer_node, timer_driver)
        timer_system.add_client(blk_driver)
        if board.arch == SystemDescription.Arch.X86_64:
            hpet_irq = SystemDescription.IrqMsi(
                pci_bus=0, pci_device=0, pci_func=0, vector=0, handle=0, id=0
            )
            timer_driver.add_irq(hpet_irq)

            hpet_regs = SystemDescription.MemoryRegion(
                sdf, "hpet_regs", 0x1000, paddr=0xFED00000
            )
            hpet_regs_map = SystemDescription.Map(
                hpet_regs, 0x5000_0000, "rw", cached=False
            )
            timer_driver.add_map(hpet_regs_map)
            sdf.add_mr(hpet_regs)

    blk_system = Sddf.Blk(sdf, blk_node, blk_driver, blk_virt)
    partition = int(args.partition) if args.partition else board.partition
    blk_system.add_client(client, partition=partition)

    if nvme:
        # Queue descriptors accessed via DMA so we map these regions as uncached.
        if board.arch == SystemDescription.Arch.RISCV64:
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
            mr = SystemDescription.MemoryRegion(sdf, name, size, paddr=paddr)
            sdf.add_mr(mr)
            blk_driver.add_map(SystemDescription.Map(mr, vaddr, "rw", cached=False))

        if board.arch == SystemDescription.Arch.X86_64:
            # BAR0: MMIO (always uncached)
            nvme_bar0_mr = SystemDescription.MemoryRegion(
                sdf, "nvme_bar0", 0x4000, paddr=0xFEBD4000
            )

            # IRQ
            nvme_irq = SystemDescription.IrqIoapic(ioapic_id=0, pin=10, vector=1, id=17)

        elif board.arch == SystemDescription.Arch.AARCH64:
            # BAR0: MMIO (always uncached)
            nvme_bar0_mr = SystemDescription.MemoryRegion(
                sdf, "nvme_bar0", 0x4000, paddr=0x10000000
            )

            # ECAM config page: MMIO (always uncached)
            nvme_ecam_mr = SystemDescription.MemoryRegion(
                sdf, "nvme_ecam", 0x1000, paddr=0x4010020000
            )
            sdf.add_mr(nvme_ecam_mr)
            blk_driver.add_map(
                SystemDescription.Map(nvme_ecam_mr, 0x20300000, "rw", cached=False)
            )

            # IRQ: slot 4 INT_A -> PCI irq line (1+4)%4 = 1 -> SPI 3 -> GIC IRQ 35
            nvme_irq = SystemDescription.IrqConventional(irq=35, id=35)

        else:  # board.arch == SystemDescription.Arch.RISCV64:
            # BAR0: MMIO (always uncached)
            nvme_bar0_mr = SystemDescription.MemoryRegion(
                sdf, "nvme_bar0", 0x4000, paddr=0x40000000
            )

            # ECAM config page: MMIO (always uncached)
            nvme_ecam_mr = SystemDescription.MemoryRegion(
                sdf, "nvme_ecam", 0x1000, paddr=0x30020000
            )
            sdf.add_mr(nvme_ecam_mr)
            blk_driver.add_map(
                SystemDescription.Map(nvme_ecam_mr, 0x20300000, "rw", cached=False)
            )

            # IRQ: slot 4 INT_A -> PCI irq line (0+4)%4 = 0 -> PLIC IRQ 0x20 = 32
            nvme_irq = SystemDescription.IrqConventional(irq=32, id=32)

        sdf.add_mr(nvme_bar0_mr)
        blk_driver.add_map(
            SystemDescription.Map(nvme_bar0_mr, 0x20000000, "rw", cached=False)
        )

        blk_driver.add_irq(nvme_irq)

    if board.arch == SystemDescription.Arch.X86_64:
        # IO ports
        pci_config_addr_port = SystemDescription.IoPort(0xCF8, 4, 1)
        blk_driver.add_ioport(pci_config_addr_port)

        pci_config_data_port = SystemDescription.IoPort(0xCFC, 4, 2)
        blk_driver.add_ioport(pci_config_data_port)

        # x86 virtio regions
        if not nvme:
            blk_requests_mr = SystemDescription.MemoryRegion(
                sdf, "virtio_requests", 65536, paddr=0x5FDF0000
            )
            sdf.add_mr(blk_requests_mr)
            blk_requests_map = SystemDescription.Map(blk_requests_mr, 0x20200000, "rw")
            blk_driver.add_map(blk_requests_map)

            blk_virtio_metadata_mr = SystemDescription.MemoryRegion(
                sdf, "virtio_metadata", 65536, paddr=0x5FFF0000
            )
            sdf.add_mr(blk_virtio_metadata_mr)
            blk_virtio_metadata_map = SystemDescription.Map(
                blk_virtio_metadata_mr, 0x20210000, "rw"
            )
            blk_driver.add_map(blk_virtio_metadata_map)

            virtio_blk_regs = SystemDescription.MemoryRegion(
                sdf, "virtio_blk_regs", 0x4000, paddr=0xFE000000
            )
            sdf.add_mr(virtio_blk_regs)
            virtio_blk_regs_map = SystemDescription.Map(
                virtio_blk_regs, 0x6000_0000, "rw", cached=False
            )
            blk_driver.add_map(virtio_blk_regs_map)

            virtio_blk_irq = SystemDescription.IrqIoapic(
                ioapic_id=0, pin=11, vector=1, id=17
            )
            blk_driver.add_irq(virtio_blk_irq)

    serial_system.add_client(client)

    pds = [serial_driver, serial_virt_tx, blk_driver, blk_virt, client]
    if need_timer:
        pds += [timer_driver]
    for pd in pds:
        sdf.add_pd(pd)

    assert blk_system.connect()
    assert blk_system.serialise_config(output_dir)
    assert serial_system.connect()
    assert serial_system.serialise_config(output_dir)
    if need_timer:
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
    parser.add_argument("--need_timer", action="store_true", default=False)
    parser.add_argument("--nvme", action="store_true", default=False)
    parser.add_argument("--partition")

    args = parser.parse_args()

    board = next(filter(lambda b: b.name == args.board, BOARDS))

    sdf = SystemDescription(board.arch, board.paddr_top)
    sddf = Sddf(args.sddf)

    dtb = None
    if board.arch != SystemDescription.Arch.X86_64:
        with open(args.dtb, "rb") as f:
            dtb = DeviceTree(f.read())

    generate(args.sdf, args.output, dtb, args.need_timer, args.nvme)
