# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause
import argparse
from typing import List
from dataclasses import dataclass
from sdfgen import SystemDescription, Sddf, DeviceTree
from importlib.metadata import version

assert version('sdfgen').split(".")[1] == "24", "Unexpected sdfgen version"

ProtectionDomain = SystemDescription.ProtectionDomain

@dataclass
class RegRegion:
    start_paddr: int
    size: int

@dataclass
class Board:
    name: str
    arch: SystemDescription.Arch
    paddr_top: int
    serial: str

BOARDS: List[Board] = [
    Board(
        name="maaxboard",
        arch=SystemDescription.Arch.AARCH64,
        paddr_top=0xa_000_000,
        serial="soc@0/bus@30800000/serial@30860000",
    ),
    Board(
        name="imx8mm_evk",
        arch=SystemDescription.Arch.AARCH64,
        paddr_top=0xa_000_000,
        serial="soc@0/bus@30800000/spba-bus@30800000/serial@30890000",
    ),
    Board(
        name="imx8mp_evk",
        arch=SystemDescription.Arch.AARCH64,
        paddr_top=0xa_000_000,
        serial="soc@0/bus@30800000/spba-bus@30800000/serial@30890000",
    ),
    Board(
        name="imx8mq_evk",
        arch=SystemDescription.Arch.AARCH64,
        paddr_top=0xa_000_000,
        serial="soc@0/bus@30800000/serial@30860000",
    ),
]


def generate(sdf_file: str, output_dir: str, dtb: DeviceTree):
    # Ensure the priority is exclusively the highest as the pinctrl driver must run first!
    pinctrl_driver = ProtectionDomain("pinctrl_driver", "pinctrl_driver.elf", priority=254)
    iomuxc_regs = SystemDescription.MemoryRegion("iomuxc_regs", 0x10000, paddr=0x30330000)
    iomuxc_gpr_regs = SystemDescription.MemoryRegion("iomuxc_gpr_regs", 0x10000, paddr=0x30340000)
    iomuxc_regs_map = SystemDescription.Map(iomuxc_regs, 0x20000000, "rw", cached=False)
    iomuxc_gpr_regs_map = SystemDescription.Map(iomuxc_gpr_regs, 0x20010000, "rw", cached=False)
    pinctrl_driver.add_map(iomuxc_regs_map)
    pinctrl_driver.add_map(iomuxc_gpr_regs_map)

    serial_driver = ProtectionDomain("serial_driver", "serial_driver.elf", priority=200)
    # Increase the stack size as running with UBSAN uses more stack space than normal.
    serial_virt_tx = ProtectionDomain("serial_virt_tx", "serial_virt_tx.elf",
                                      priority=199, stack_size=0x2000)
    serial_virt_rx = ProtectionDomain("serial_virt_rx", "serial_virt_rx.elf",
                                      priority=199, stack_size=0x2000)
    client0 = ProtectionDomain("client", "client.elf", priority=1)

    serial_node = dtb.node(board.serial)
    assert serial_node is not None

    serial_system = Sddf.Serial(sdf, serial_node, serial_driver,
                                serial_virt_tx, virt_rx=serial_virt_rx)
    serial_system.add_client(client0)

    pds = [
        pinctrl_driver,
        serial_driver,
        serial_virt_tx,
        serial_virt_rx,
        client0,
    ]
    for pd in pds:
        sdf.add_pd(pd)

    sdf.add_mr(iomuxc_regs)
    sdf.add_mr(iomuxc_gpr_regs)

    assert serial_system.connect()
    assert serial_system.serialise_config(output_dir)

    with open(f"{output_dir}/{sdf_file}", "w+") as f:
        f.write(sdf.render())


if __name__ == '__main__':
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
