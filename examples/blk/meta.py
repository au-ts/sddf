# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause
import argparse
from typing import List, Optional
from dataclasses import dataclass
from sdfgen import SystemDescription, Sddf, DeviceTree
from importlib.metadata import version

# assert version('sdfgen').split(".")[1] == "24", "Unexpected sdfgen version"

ProtectionDomain = SystemDescription.ProtectionDomain
IrqIoapic = SystemDescription.IrqIoapic

@dataclass
class Board:
    name: str
    arch: SystemDescription.Arch
    paddr_top: int
    blk: Optional[str]
    # Default partition if the user has not specified one
    partition: int
    # Use actual serial driver for output, so we can test non-debug configurations
    serial: Optional[str]
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
        serial="pl011@9000000",
        timer=None,
    ),
    Board(
        name="maaxboard",
        arch=SystemDescription.Arch.AARCH64,
        paddr_top=0x7_0000_000,
        partition=2,
        blk="soc@0/bus@30800000/mmc@30b40000",
        timer="soc@0/bus@30000000/timer@302d0000",
        serial="soc@0/bus@30800000/serial@30860000",
    ),
    Board(
        name="qemu_virt_riscv64",
        arch=SystemDescription.Arch.RISCV64,
        paddr_top=0xa_0000_000,
        partition=0,
        blk="soc/virtio_mmio@10008000",
        serial="soc/serial@10000000",
        timer=None,
    ),
    Board(
        name="x86_64_generic",
        arch=SystemDescription.Arch.X86_64,
        paddr_top=0x20000000,
        partition=0, # @Trsitan : todo , figure out what linux does and implications
        blk=None,
        serial=None,
        timer=None,
    )
]


def generate(sdf_file: str, output_dir: str, dtb: Optional[DeviceTree]):
    blk_node = None
    serial_node = None
    if dtb is not None:
        serial_node = dtb.node(board.serial)
        assert serial_node is not None
        blk_node = dtb.node(board.blk)
        assert blk_node is not None

    serial_driver = ProtectionDomain("serial_driver", "serial_driver.elf", priority=200)
    # Increase the stack size as running with UBSAN uses more stack space than normal.
    serial_virt_tx = ProtectionDomain("serial_virt_tx", "serial_virt_tx.elf",
                                      priority=199, stack_size=0x2000)
    serial_system = Sddf.Serial(sdf, serial_node, serial_driver, serial_virt_tx, enable_color=False)

    if board.arch == SystemDescription.Arch.X86_64:
        serial_port = SystemDescription.IoPort(SystemDescription.Arch.X86_64, 0x3f8, 8, 0)
        serial_driver.add_ioport(serial_port)

    blk_driver = ProtectionDomain("blk_driver", "blk_driver.elf", priority=200, stack_size=0x2000)
    blk_virt = ProtectionDomain("blk_virt", "blk_virt.elf", priority=199, stack_size=0x2000)
    client = ProtectionDomain("client", "client.elf", priority=1)

    if dtb is not None and board.timer:
        timer_node = dtb.node(board.timer)
        assert timer_node is not None

        timer_driver = ProtectionDomain("timer_driver", "timer_driver.elf", priority=201)
        timer_system = sddf.Timer(sdf, timer_node, timer_driver)
        timer_system.add_client(blk_driver)

    # @Tristan: do this a better way
    if board.arch == SystemDescription.Arch.X86_64:
        timer_node = None
        timer_driver = ProtectionDomain("timer_driver", "timer_driver.elf", priority=201)
        timer_system = sddf.Timer(sdf, timer_node, timer_driver)

        hept_irq = SystemDescription.IrqMsi(board.arch, 0, 0, 0, 0, 0, 0)
        timer_driver.add_irq(hept_irq)

        hept_regs = SystemDescription.MemoryRegion(sdf, "hept_regs", 0x1000, paddr=0xfed00000)
        hept_regs_map = SystemDescription.Map(hept_regs, 0x5_0000_0000, "rw", cached=False)
        timer_driver.add_map(hept_regs_map)
        sdf.add_mr(hept_regs)

        timer_system.add_client(blk_driver)

    blk_system = Sddf.Blk(sdf, blk_node, blk_driver, blk_virt)

    if board.arch == SystemDescription.Arch.X86_64:
        pci_ecam = SystemDescription.MemoryRegion(sdf, "pci_ecam", 0x10000000, paddr=0xe0000000)
        pci_ecam_map = SystemDescription.Map(pci_ecam, 0x6_0000_0000, "rw", cached=False)
        blk_driver.add_map(pci_ecam_map)
        sdf.add_mr(pci_ecam)

        # The last PCI base address register, BAR[5], points to the AHCI base memory, it’s called ABAR (AHCI Base Memory Register).
        sata_controller_bar_5 = SystemDescription.MemoryRegion(sdf, "sata_controller_bar_5", 0x1000, paddr=0xb0402000)
        sata_controller_bar_5_map = SystemDescription.Map(sata_controller_bar_5, 0x7_0000_0000, "rw", cached=False)
        blk_driver.add_map(sata_controller_bar_5_map)
        sdf.add_mr(sata_controller_bar_5)

        # We can cache all of these as true

        # We only use one port in the example (1 device)
        ahci_command_list = SystemDescription.MemoryRegion(sdf, "ahci_command_list", 0x1000, paddr=0x10000000)
        ahci_command_list_map = SystemDescription.Map(ahci_command_list, 0x7_2000_0000, "rw", cached=True)
        blk_driver.add_map(ahci_command_list_map)
        sdf.add_mr(ahci_command_list)

        ahci_FIS = SystemDescription.MemoryRegion(sdf, "ahci_FIS", 0x1000, paddr=0x10002000)
        ahci_FIS_map = SystemDescription.Map(ahci_FIS, 0x7_2000_2000, "rw", cached=True)
        blk_driver.add_map(ahci_FIS_map)
        sdf.add_mr(ahci_FIS)

        # There are 32 possible command tables
        # We just map them all contiguously

        # Command tables can support up to 65535 PRDT entries
        # for now we just use 8 which should be enough for most use cases

        # if its only got 8 then the size for each table becomes
        # 128 (header) + 8 * 16 (PRDT) = 256 bytes each

        ahci_command_tables = SystemDescription.MemoryRegion(sdf, "ahci_command_tables", 0x2000, paddr=0x10004000)
        ahci_command_tables_map = SystemDescription.Map(ahci_command_tables, 0x7_2000_4000, "rw", cached=True)
        blk_driver.add_map(ahci_command_tables_map)
        sdf.add_mr(ahci_command_tables)

        # Just for testing and first iterations of the driver before using virt and client
        data_region = SystemDescription.MemoryRegion(sdf, "data_region", 0x10_000, paddr=0x10008000)
        data_region_map = SystemDescription.Map(data_region, 0x7_2000_8000, "rw", cached=True)
        blk_driver.add_map(data_region_map)
        sdf.add_mr(data_region)

        # This is for the identify command which we need DMA for
        identify_command = SystemDescription.MemoryRegion(sdf, "identify_command", 0x1000, paddr=0x10020000)
        identify_command_map = SystemDescription.Map(identify_command, 0x7_2002_0000, "rw", cached=True)
        blk_driver.add_map(identify_command_map)
        sdf.add_mr(identify_command)

        irq = IrqIoapic(
            arch=SystemDescription.Arch.X86_64,
            ioapic_id=0, # from Linux
            pin=16, # from Linux
            vector=64,  # arbitrary
            trigger=IrqIoapic.Trigger.LEVEL,
            polarity=IrqIoapic.Polarity.ACTIVELOW,
            id=60
        )
        blk_driver.add_irq(irq)

    partition = int(args.partition) if args.partition else board.partition
    blk_system.add_client(client, partition=partition)

    serial_system.add_client(client)

    pds = [
        serial_driver,
        serial_virt_tx,
        blk_driver,
        blk_virt,
        client
    ]
    if dtb is not None and board.timer:
        pds += [timer_driver]

    # @Tristan: do this a better way
    if board.arch == SystemDescription.Arch.X86_64:
         pds += [timer_driver]

    for pd in pds:
        sdf.add_pd(pd)

    assert blk_system.connect()
    assert blk_system.serialise_config(output_dir)
    assert serial_system.connect()
    assert serial_system.serialise_config(output_dir)
    if dtb is not None and board.timer:
        assert timer_system.connect()
        assert timer_system.serialise_config(output_dir)

    # @Tristan: do this a better way
    if board.arch == SystemDescription.Arch.X86_64:
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

    dtb = None
    if board.arch != SystemDescription.Arch.X86_64:
        with open(args.dtb, "rb") as f:
            dtb = DeviceTree(f.read())

    generate(args.sdf, args.output, dtb)
