# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause
import argparse
import sys
import os
from typing import List
from dataclasses import dataclass
from sdfgen import SystemDescription, Sddf, DeviceTree
from importlib.metadata import version

sys.path.append(
    os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../tools/meta")
)
from board import BOARDS

assert version("sdfgen").split(".")[1] == "28", "Unexpected sdfgen version"

ProtectionDomain = SystemDescription.ProtectionDomain
Irq = SystemDescription.Irq
MemoryRegion = SystemDescription.MemoryRegion
Map = SystemDescription.Map



def generate(sdf_file: str, output_dir: str, dtb: DeviceTree):
    gpio_driver = ProtectionDomain("gpio_driver", "gpio_driver.elf", priority=254)
    client = ProtectionDomain("client", "client.elf", priority=1)

    gpio_node = dtb.node(board.gpio)
    assert gpio_node is not None

    gpio_system = Sddf.Gpio(sdf, gpio_node, gpio_driver)

    # These need to be different to the ones hardcoded in config.json or this file
    driver_channel_ids = [0, 1]
    gpio_system.add_client(client, driver_channel_ids=driver_channel_ids)

    # We need a timer driver for the example
    timer_driver = ProtectionDomain("timer_driver", "timer_driver.elf", priority=254)
    timer_node = dtb.node(board.timer)
    assert timer_node is not None
    timer_system = Sddf.Timer(sdf, timer_node, timer_driver)
    timer_system.add_client(client)

    pds = [gpio_driver, timer_driver, client]
    for pd in pds:
        sdf.add_pd(pd)

    # TODO: currently there is no check to see if driver_channel_ids hasn't chosen a channel used
    # by a device irq
    # But it will still fail really deep inside of gpio_system.connect() and not compile

    assert gpio_system.connect()
    assert gpio_system.serialise_config(output_dir)

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

    args = parser.parse_args()

    board = next(filter(lambda b: b.name == args.board, BOARDS))

    sdf = SystemDescription(board.arch, board.paddr_top)
    sddf = Sddf(args.sddf)

    with open(args.dtb, "rb") as f:
        dtb = DeviceTree(f.read())

    generate(args.sdf, args.output, dtb)
