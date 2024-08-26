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

assert version("sdfgen").split(".")[1] == "27", "Unexpected sdfgen version"

ProtectionDomain = SystemDescription.ProtectionDomain


def generate(sdf_file: str, output_dir: str, dtb: DeviceTree, need_timer: bool):
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
    if need_timer:
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
    parser.add_argument("--dtb", required=True)
    parser.add_argument("--sddf", required=True)
    parser.add_argument("--board", required=True, choices=[b.name for b in BOARDS])
    parser.add_argument("--output", required=True)
    parser.add_argument("--sdf", required=True)
    parser.add_argument("--need_timer", action="store_true", default=False)
    parser.add_argument("--partition")

    args = parser.parse_args()

    board = next(filter(lambda b: b.name == args.board, BOARDS))

    sdf = SystemDescription(board.arch, board.paddr_top)
    sddf = Sddf(args.sddf)

    with open(args.dtb, "rb") as f:
        dtb = DeviceTree(f.read())

    generate(args.sdf, args.output, dtb, args.need_timer)
