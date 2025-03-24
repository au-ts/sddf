# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause
import argparse
from typing import List, Optional
from dataclasses import dataclass
from sdfgen import SystemDescription, Sddf, DeviceTree
from importlib.metadata import version

assert version("sdfgen").split(".")[1] == "27", "Unexpected sdfgen version"

ProtectionDomain = SystemDescription.ProtectionDomain
MemoryRegion = SystemDescription.MemoryRegion
Map = SystemDescription.Map

@dataclass
class Board:
    name: str
    arch: SystemDescription.Arch
    paddr_top: int
    blk: str
    # Default partition if the user has not specified one
    partition: int
    # Use actual serial driver for output, so we can test non-debug configurations
    serial: str
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
        name="odroidc4",
        arch=SystemDescription.Arch.AARCH64,
        paddr_top=0x80000000,
        partition=0,
        blk="soc/sd@ffe05000",
        timer=None,
    ),
    Board(
        name="odroidc4",
        arch=SystemDescription.Arch.AARCH64,
        paddr_top=0x80000000,
        partition=0,
        blk="soc/sd@ffe05000",
        timer=None,
    ),
    Board(
        name="qemu_virt_riscv64",
        arch=SystemDescription.Arch.RISCV64,
        paddr_top=0xA_0000_000,
        partition=0,
        blk="soc/virtio_mmio@10008000",
        serial="soc/serial@10000000",
        timer=None,
    ),
]


def generate(sdf_file: str, output_dir: str, dtb: DeviceTree):
    serial_driver = ProtectionDomain("serial_driver", "serial_driver.elf", priority=200)
    # Increase the stack size as running with UBSAN uses more stack space than normal.
    serial_virt_tx = ProtectionDomain(
        "serial_virt_tx", "serial_virt_tx.elf", priority=199, stack_size=0x2000
    )

    serial_node = dtb.node(board.serial)
    assert serial_node is not None

    serial_system = Sddf.Serial(
        sdf, serial_node, serial_driver, serial_virt_tx, enable_color=False
    )

    blk_driver = ProtectionDomain(
        "blk_driver", "blk_driver.elf", priority=200, stack_size=0x2000
    )
    blk_virt = ProtectionDomain(
        "blk_virt", "blk_virt.elf", priority=199, stack_size=0x2000
    )
    client = ProtectionDomain("client", "client.elf", priority=1)

    blk_node = dtb.node(board.blk)
    assert blk_node is not None
    if board.timer:
        timer_node = dtb.node(board.timer)
        assert timer_node is not None

        timer_driver = ProtectionDomain(
            "timer_driver", "timer_driver.elf", priority=201
        )
        timer_system = sddf.Timer(sdf, timer_node, timer_driver)
        timer_system.add_client(blk_driver)

    blk_system = Sddf.Blk(sdf, blk_node, blk_driver, blk_virt)
    partition = int(args.partition) if args.partition else board.partition
    blk_system.add_client(client, partition=partition)

    if board.name == "odroidc4":
        gpio_mr = MemoryRegion("gpio", 0x1000, paddr=0xff800000)
        blk_driver.add_map(Map(gpio_mr, 0xff800000, "rw", cached=False))
        sdf.add_mr(gpio_mr)

    serial_system.add_client(client)

    pds = [serial_driver, serial_virt_tx, blk_driver, blk_virt, client]
    if board.timer:
        pds += [timer_driver]
    for pd in pds:
        sdf.add_pd(pd)

    assert blk_system.connect()
    assert blk_system.serialise_config(output_dir)
    assert serial_system.connect()
    assert serial_system.serialise_config(output_dir)
    if board.timer:
        assert timer_system.connect()
        assert timer_system.serialise_config(output_dir)

    with open(f"{output_dir}/{sdf_file}", "w+") as f:
        f.write(sdf.render())


if __name__ == "__main__":
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

    with open(args.dtb, "rb") as f:
        dtb = DeviceTree(f.read())

    generate(args.sdf, args.output, dtb)
