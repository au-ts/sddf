# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause
import os, sys
import struct
import subprocess
import argparse
from typing import List, Optional
from dataclasses import dataclass
from sdfgen import SystemDescription, Sddf, DeviceTree

sys.path.append(
    os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../tools/meta")
)
from board import BOARDS, add_x86_hpet

ProtectionDomain = SystemDescription.ProtectionDomain
MemoryRegion = SystemDescription.MemoryRegion
CNode = SystemDescription.CNode
Map = SystemDescription.Map
CapMap = SystemDescription.CapMap
BootInfo = SystemDescription.BootInfo
Channel = SystemDescription.Channel
IrqIoapic = SystemDescription.IrqIoapic


# Assumes elf string has ".elf" suffix, adds ".data" to data string
def update_elf_section(
    elf_name: str, section_name: str, data_name: str, data_number=None
):
    assert os.path.isfile(elf_name)
    if data_number != None:
        data_name += str(data_number)
    data_name += ".data"
    assert os.path.isfile(data_name)
    assert (
        subprocess.run(
            [
                obj_copy,
                "--update-section",
                "." + section_name + "=" + data_name,
                elf_name,
            ]
        ).returncode
        == 0
    )


class AcpiTablesConfig:
    def __init__(
        self,
        max_total_size: int,
    ):
        self.max_total_size = max_total_size
        self.patched_tables_end = 0
        self.alignment = 0x1000
        self.max_num_acpi_tables = 20 # This needs to be synced with MAX_NUM_ACPI_TABLES in acpi.h
        self.num_tables = 0
        self.acpi_table_bytes = bytearray()
        self.acpi_table_pointers = [0] * self.max_num_acpi_tables

    # TODO: add the checks
    def add_acpi_table(self, acpi_file):
        acpi_file = "/Users/terrybai/tmp/acpi_vb105/vb105_acpi/" + acpi_file + ".dat"
        print(acpi_file)
        assert os.path.isfile(acpi_file)
        with open(acpi_file, "rb") as data_file:
            byte_list = list(data_file.read())

            if len(byte_list) + len(self.acpi_table_bytes) < self.max_total_size:
                self.acpi_table_pointers[self.num_tables] = len(self.acpi_table_bytes)
                self.acpi_table_bytes.extend(byte_list)
                self.patched_tables_end = len(self.acpi_table_bytes)
                self.num_tables += 1

        trailing_len = len(self.acpi_table_bytes) % self.alignment
        if trailing_len != 0:
            padding_len = self.alignment - trailing_len
            if padding_len + len(self.acpi_table_bytes) < self.max_total_size:
                self.acpi_table_bytes.extend(b"\x00" * padding_len)

    def tables_serialise(self):
        pack_str = "<" + "B" * len(self.acpi_table_bytes)

        return struct.pack(
            pack_str,
            *self.acpi_table_bytes
        )

    def summary_serialise(self):
        pack_str = "<" + "Q" * self.max_num_acpi_tables + "QQII"

        return struct.pack(
            pack_str,
            *self.acpi_table_pointers,
            self.patched_tables_end,
            self.max_total_size,
            self.alignment,
            self.num_tables,
        )

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
            "timer_driver", "timer_driver.elf", priority=253
        )
        if board.arch == SystemDescription.Arch.X86_64:
            add_x86_hpet(sdf, timer_driver)

        timer_system = sddf.Timer(sdf, timer_node, timer_driver)
        timer_system.add_client(blk_driver)


    blk_system = Sddf.Blk(sdf, blk_node, blk_driver, blk_virt)
    partition = int(args.partition) if args.partition else board.partition
    blk_system.add_client(client, partition=partition)

    acpi_driver = ProtectionDomain("acpi_driver", "acpi_driver.elf", priority=211, stack_size=0x5000)
    pci_driver = ProtectionDomain("pci_driver", "pci_driver.elf", priority=210)

    acpi_bootinfo_post_capdl_untypeds = MemoryRegion(sdf, "bootinfo_post_capdl_untypeds", 0x1000, prefill_bootinfo="post_capdl_untypeds")
    sdf.add_mr(acpi_bootinfo_post_capdl_untypeds)
    acpi_driver.add_map(Map(acpi_bootinfo_post_capdl_untypeds, 0x2000000, "r", setvar_vaddr="bootinfo_post_capdl_untypeds"))

    acpi_bootinfo_rsdp = MemoryRegion(sdf, "bootinfo_rsdp", 0x1000, prefill_bootinfo="x86_acpi_rsdp")
    sdf.add_mr(acpi_bootinfo_rsdp)
    acpi_driver.add_map(Map(acpi_bootinfo_rsdp, 0x2001000, "r", setvar_vaddr="bootinfo_rsdp"))

    acpi_tables_config = AcpiTablesConfig(0x500000)
    # acpi_tables_config.add_acpi_table("mcfg")
    # acpi_tables_config.add_acpi_table("dsdt")
    # for i in range(1, 18):
    #     acpi_tables_config.add_acpi_table("ssdt" + str(i))

    # acpi_driver.add_boot_info(BootInfo("remaining_untypeds"))
    # acpi_driver.add_boot_info(BootInfo("rsdp"))

    cnode_remaining_untypeds = CNode("remaining_untypeds", True, 9)
    sdf.add_cnode(cnode_remaining_untypeds)
    acpi_driver.add_cap_map(CapMap(CapMap.CapType.Cnode, None, cnode_remaining_untypeds, 1))
    acpi_driver.add_cap_map(CapMap(CapMap.CapType.Vspace, pci_driver, None, 2))

    cnode_pci_resources = CNode("pci_resources", False, 9)
    sdf.add_cnode(cnode_pci_resources)
    acpi_driver.add_cap_map(CapMap(CapMap.CapType.Cnode, None, cnode_pci_resources, 3))
    pci_driver.add_cap_map(CapMap(CapMap.CapType.Cnode, None, cnode_pci_resources, 1))

    mr_aml_object_pool = MemoryRegion(sdf, "aml_object_pool", 0x100000)
    sdf.add_mr(mr_aml_object_pool)
    acpi_driver.add_map(Map(mr_aml_object_pool, 0x30000000, "rw"))

    mr_aml_state_stack = MemoryRegion(sdf, "aml_state_stack", 0x10000)
    sdf.add_mr(mr_aml_state_stack)
    acpi_driver.add_map(Map(mr_aml_state_stack, 0x50000000, "rw"))

    mr_acpi_tables_copy = MemoryRegion(sdf, "acpi_tables_copy", 0x50000)
    sdf.add_mr(mr_acpi_tables_copy)
    acpi_driver.add_map(Map(mr_acpi_tables_copy, 0x40000000, "rw"))

    mr_pci_resources = MemoryRegion(sdf, "pci_resources", 0x40000)
    sdf.add_mr(mr_pci_resources)
    acpi_driver.add_map(Map(mr_pci_resources, 0x60000000, "rw", cached=False))
    pci_driver.add_map(Map(mr_pci_resources, 0x60000000, "rw", cached=False))

    sdf.add_channel(Channel(acpi_driver, pci_driver, a_id=0, b_id=0))

    pci_driver.add_cap_map(CapMap(CapMap.CapType.Vspace, blk_driver, None, 2))
    pci_driver.add_cap_map(CapMap(CapMap.CapType.Cspace, blk_driver, None, 3))
    sdf.add_channel(Channel(pci_driver, blk_driver, a_id=1, b_id=10))

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

        if board.name == "qemu_virt_x86":
            # BAR0: MMIO (always uncached)
            nvme_bar0_mr = SystemDescription.MemoryRegion(
                sdf, "nvme_bar0", 0x4000, paddr=0xFEBD4000
            )

            # IRQ
            nvme_irq = SystemDescription.IrqIoapic(ioapic_id=0,
                                                   pin=10,
                                                   vector=1,
                                                   trigger=IrqIoapic.Trigger.LEVEL,
                                                   polarity=IrqIoapic.Polarity.ACTIVELOW,
                                                   id=17)

        elif board.name == "vb_105" or board.name == 'viscous':
            # BAR0: MMIO (always uncached)
            # nvme_bar0_mr = SystemDescription.MemoryRegion(
            #     # sdf, "nvme_bar0", 0x4000, paddr=0x8f800000
            #     sdf, "nvme_bar0", 0x4000, paddr=0x92100000
            # )
            # IRQ
            # nvme_irq = SystemDescription.IrqIoapic(ioapic_id=0,
            #                                        pin=16,
            #                                        vector=1,
            #                                        trigger=IrqIoapic.Trigger.LEVEL,
            #                                        polarity=IrqIoapic.Polarity.ACTIVELOW,
            #                                        id=17)
            blk_driver.add_irq_placeholder(17)


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

        if 'nvme_bar0_mr' in locals():
            sdf.add_mr(nvme_bar0_mr)
            blk_driver.add_map(
                SystemDescription.Map(nvme_bar0_mr, 0x20000000, "rw", cached=False)
            )

        if 'nvme_irq' in locals():
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

    pds = [serial_driver, serial_virt_tx, blk_driver, blk_virt, client, acpi_driver, pci_driver]
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

    with open(f"{output_dir}/acpi_tables_summary.data", "wb+") as f:
        f.write(acpi_tables_config.summary_serialise())
    update_elf_section("acpi_driver.elf", "acpi_tables_summary", "acpi_tables_summary")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--dtb", required=False)
    parser.add_argument("--sddf", required=True)
    parser.add_argument("--board", required=True, choices=[b.name for b in BOARDS])
    parser.add_argument("--output", required=True)
    parser.add_argument("--sdf", required=True)
    parser.add_argument("--need_timer", action="store_true", default=False)
    parser.add_argument("--objcopy", required=True)
    parser.add_argument("--nvme", action="store_true", default=False)
    parser.add_argument("--partition")

    args = parser.parse_args()

    board = next(filter(lambda b: b.name == args.board, BOARDS))

    sdf = SystemDescription(board.arch, board.paddr_top)
    sddf = Sddf(args.sddf)

    global obj_copy
    obj_copy = args.objcopy

    dtb = None
    if board.arch != SystemDescription.Arch.X86_64:
        with open(args.dtb, "rb") as f:
            dtb = DeviceTree(f.read())

    generate(args.sdf, args.output, dtb, args.need_timer, args.nvme)
