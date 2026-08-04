# Copyright 2026, UNSW
# SPDX-License-Identifier: BSD-2-Clause
import os
import sys
import argparse
from sdfgen import SystemDescription, Sddf, DeviceTree
from typing import List, Tuple, Callable, Optional
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


def generate(sdf_file: str, output_dir: str, dtb: Optional[DeviceTree]):
    acpi_driver = ProtectionDomain("acpi_driver", "acpi_driver.elf", priority=253)

    pds = [acpi_driver]
    for pd in pds:
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
