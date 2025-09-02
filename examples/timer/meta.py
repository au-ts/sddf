# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause
import argparse
from typing import List
from dataclasses import dataclass
from sdfgen import SystemDescription, Sddf, DeviceTree
from importlib.metadata import version

assert version("sdfgen").split(".")[1] == "26", "Unexpected sdfgen version"

ProtectionDomain = SystemDescription.ProtectionDomain


@dataclass
class Board:
    name: str
    arch: SystemDescription.Arch
    paddr_top: int
    timer: str | None


BOARDS: List[Board] = [
    Board(
        name="qemu_virt_aarch64",
        arch=SystemDescription.Arch.AARCH64,
        paddr_top=0xA_000_000,
        timer="timer",
    ),
    Board(
        name="qemu_virt_riscv64",
        arch=SystemDescription.Arch.RISCV64,
        paddr_top=0xA_0000_000,
        timer="soc/rtc@101000",
    ),
    Board(
        name="odroidc2",
        arch=SystemDescription.Arch.AARCH64,
        paddr_top=0x80000000,
        timer="soc/bus@c1100000/watchdog@98d0",
    ),
    Board(
        name="odroidc4",
        arch=SystemDescription.Arch.AARCH64,
        paddr_top=0x80000000,
        timer="soc/bus@ffd00000/watchdog@f0d0",
    ),
    Board(
        name="star64",
        arch=SystemDescription.Arch.RISCV64,
        paddr_top=0x100000000,
        timer="soc/timer@13050000",
    ),
    Board(
        name="maaxboard",
        arch=SystemDescription.Arch.AARCH64,
        paddr_top=0xA0000000,
        timer="soc@0/bus@30000000/timer@302d0000",
    ),
    Board(
        name="imx8mm_evk",
        arch=SystemDescription.Arch.AARCH64,
        paddr_top=0xA0000000,
        timer="soc@0/bus@30000000/timer@302d0000",
    ),
    Board(
        name="imx8mp_evk",
        arch=SystemDescription.Arch.AARCH64,
        paddr_top=0xA0000000,
        timer="soc@0/bus@30000000/timer@302d0000",
    ),
    Board(
        name="imx8mq_evk",
        arch=SystemDescription.Arch.AARCH64,
        paddr_top=0xA0000000,
        timer="soc@0/bus@30000000/timer@302d0000",
    ),
    Board(
        name="zcu102",
        arch=SystemDescription.Arch.AARCH64,
        paddr_top=0xA0000000,
        timer="axi/timer@ff140000",
    ),
    Board(
        name="x86_64_generic",
        arch=SystemDescription.Arch.X86_64,
        paddr_top=0x7ffdf000,
        timer=None,
    )
]


def generate(sdf_file: str, output_dir: str, dtb: DeviceTree | None):
    timer_node = None
    timer_driver = ProtectionDomain("timer_driver", "timer_driver.elf", priority=254)

    if board.name == "x86_64_generic":
        hpet_irq = SystemDescription.IrqMsi(board.arch, 0, 0, 0, 0, 0, 0)
        timer_driver.add_irq(hpet_irq)

        hept_regs = SystemDescription.MemoryRegion(sdf, "hept_regs", 0x1000, paddr=0xfed00000)
        hept_regs_map = SystemDescription.Map(hept_regs, 0x5000_0000, "rw", cached=False)
        timer_driver.add_map(hept_regs_map)
        sdf.add_mr(hept_regs)
    else:
        timer_node = dtb.node(board.timer)
        assert timer_node is not None

    client = ProtectionDomain("client", "client.elf", priority=1)

    timer_system = Sddf.Timer(sdf, timer_node, timer_driver)
    timer_system.add_client(client)

    pds = [timer_driver, client]
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
