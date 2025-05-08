# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause
import argparse
from typing import List
from dataclasses import dataclass
from sdfgen import SystemDescription, Sddf, DeviceTree
from importlib.metadata import version

# @billn fix
# assert version('sdfgen').split(".")[1] == "24", "Unexpected sdfgen version"

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
    pinctrl: str


BOARDS: List[Board] = [
    Board(
        name="maaxboard",
        arch=SystemDescription.Arch.AARCH64,
        paddr_top=0xA_000_000,
        serial="soc@0/bus@30800000/serial@30860000",
        pinctrl="soc@0/bus@30000000/iomuxc@30330000",
    ),
    Board(
        name="imx8mm_evk",
        arch=SystemDescription.Arch.AARCH64,
        paddr_top=0xA_000_000,
        serial="soc@0/bus@30800000/spba-bus@30800000/serial@30890000",
        pinctrl="soc@0/bus@30000000/pinctrl@30330000",
    ),
    Board(
        name="imx8mp_evk",
        arch=SystemDescription.Arch.AARCH64,
        paddr_top=0xA_000_000,
        serial="soc@0/bus@30800000/spba-bus@30800000/serial@30890000",
        pinctrl="soc@0/bus@30000000/pinctrl@30330000",
    ),
    Board(
        name="imx8mq_evk",
        arch=SystemDescription.Arch.AARCH64,
        paddr_top=0xA_000_000,
        serial="soc@0/bus@30800000/serial@30860000",
        pinctrl="soc@0/bus@30000000/pinctrl@30330000",
    ),
]


def generate(sdf_file: str, output_dir: str, dtb: DeviceTree):
    pinctrl_node = dtb.node(board.pinctrl)
    assert pinctrl_node is not None

    # Ensure the priority is exclusively the highest as the pinctrl driver must run first!
    # This is enforced by sdfgen at the render() step.
    pinctrl_driver = ProtectionDomain(
        "pinctrl_driver", "pinctrl_driver.elf", priority=253
    )
    pinctrl_system = Sddf.Pinctrl(sdf, pinctrl_node, pinctrl_driver)

    serial_driver = ProtectionDomain("serial_driver", "serial_driver.elf", priority=200)
    # Increase the stack size as running with UBSAN uses more stack space than normal.
    serial_virt_tx = ProtectionDomain(
        "serial_virt_tx", "serial_virt_tx.elf", priority=199, stack_size=0x2000
    )
    serial_virt_rx = ProtectionDomain(
        "serial_virt_rx", "serial_virt_rx.elf", priority=199, stack_size=0x2000
    )
    serial_client = ProtectionDomain("serial_client", "serial_client.elf", priority=1)

    serial_node = dtb.node(board.serial)
    assert serial_node is not None

    serial_system = Sddf.Serial(
        sdf,
        serial_node,
        serial_driver,
        serial_virt_tx,
        virt_rx=serial_virt_rx,
        enable_color=False,
    )
    serial_system.add_client(serial_client)

    pds = [
        pinctrl_driver,
        serial_driver,
        serial_virt_tx,
        serial_virt_rx,
        serial_client,
    ]
    for pd in pds:
        sdf.add_pd(pd)

    assert serial_system.connect()
    assert serial_system.serialise_config(output_dir)

    assert pinctrl_system.connect()
    assert pinctrl_system.serialise_config(output_dir)

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
