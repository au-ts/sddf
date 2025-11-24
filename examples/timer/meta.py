# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause
import os
import sys
import argparse
from sdfgen import SystemDescription, Sddf, DeviceTree
import importlib
from importlib.metadata import version

sys.path.append(
    os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../tools/meta")
)

# Use importlib to dynamically load. Using `from` import below other code is bad style.
board_module = importlib.import_module("board")
BOARDS = board_module.BOARDS

assert version("sdfgen").split(".")[1] == "27", "Unexpected sdfgen version"

ProtectionDomain = SystemDescription.ProtectionDomain


def generate(sdf_file: str, output_dir: str, dtb: DeviceTree):
    timer_node = None
    timer_driver = ProtectionDomain("timer_driver", "timer_driver.elf", priority=253)
    client = ProtectionDomain("client", "client.elf", priority=1)

    if board.name == "x86_64_generic":
        # actual interrupt vector = 0 + irq_user_min(0x10) + IRQ_INT_OFFSET(0x20) = 0x30
        hpet_irq = SystemDescription.IrqMsi(board.arch, 0, 0, 0, 0, 0, 0)
        timer_driver.add_irq(hpet_irq)

        hept_regs = SystemDescription.MemoryRegion(
            sdf, "hept_regs", 0x1000, paddr=0xFED00000
        )
        hept_regs_map = SystemDescription.Map(
            hept_regs, 0x5000_0000, "rw", cached=False
        )
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
