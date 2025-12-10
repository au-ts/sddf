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

assert version("sdfgen").split(".")[1] == "28", "Unexpected sdfgen version"

ProtectionDomain = SystemDescription.ProtectionDomain


def generate(sdf_file: str, output_dir: str, dtb: DeviceTree):
    client = ProtectionDomain("client", "client.elf", priority=1)

    pcie_driver = ProtectionDomain("pcie_driver", "pcie_driver.elf", priority=252)
    ecam_mr = SystemDescription.MemoryRegion(sdf, "ecam_regs", 0x10000000, paddr=0xb0000000)
    bios_mr = SystemDescription.MemoryRegion(sdf, "bios_regs", 0x20000, paddr=0xe0000)
    sdt_mr = SystemDescription.MemoryRegion(sdf, "sdt_regs", 0x100000, paddr=0x7f00000)
    sdf.add_mr(ecam_mr)
    sdf.add_mr(bios_mr)
    sdf.add_mr(sdt_mr)
    pcie_driver.add_map(SystemDescription.Map(ecam_mr, 0xb0000000, "rw"))
    pcie_driver.add_map(SystemDescription.Map(bios_mr, 0xe0000, "rw"))
    pcie_driver.add_map(SystemDescription.Map(sdt_mr, 0x7f00000, "rw"))

    pds = [client, pcie_driver]
    for pd in pds:
        print("add pd")
        sdf.add_pd(pd)

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
