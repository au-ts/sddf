# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause
import argparse
from typing import List
from dataclasses import dataclass
from sdfgen import SystemDescription, Sddf, DeviceTree

ProtectionDomain = SystemDescription.ProtectionDomain
MemoryRegion = SystemDescription.MemoryRegion
Map = SystemDescription.Map


@dataclass
class Board:
    name: str
    arch: SystemDescription.Arch
    paddr_top: int
    i2c: str
    timer: str


BOARDS: List[Board] = [
    Board(
        name="odroidc4",
        arch=SystemDescription.Arch.AARCH64,
        paddr_top=0x80000000,
        i2c="soc/bus@ffd00000/i2c@1d000",
        timer="soc/bus@ffd00000/watchdog@f0d0",
    ),
]


def generate(sdf_file: str, output_dir: str, dtb: DeviceTree):
    timer_driver = ProtectionDomain("timer_driver", "timer_driver.elf", priority=4)
    i2c_driver = ProtectionDomain("i2c_driver", "i2c_driver.elf", priority=3)
    i2c_virt = ProtectionDomain("i2c_virt", "i2c_virt.elf", priority=2)
    client_pn532 = ProtectionDomain("client_pn532", "client_pn532.elf", priority=1)
    client_ds3231 = ProtectionDomain("client_ds3231", "client_ds3231.elf", priority=1)

    # Right now we do not have separate clk and GPIO drivers and so our I2C driver does manual
    # clk/GPIO setup for I2C.
    clk_mr = MemoryRegion("clk", 0x1000, paddr=0xff63c000)
    gpio_mr = MemoryRegion("gpio", 0x1000, paddr=0xff634000)
    sdf.add_mr(clk_mr)
    sdf.add_mr(gpio_mr)

    i2c_driver.add_map(Map(clk_mr, 0x30_000_000, "rw", cached=False))
    i2c_driver.add_map(Map(gpio_mr, 0x30_100_000, "rw", cached=False))

    i2c_node = dtb.node(board.i2c)
    assert i2c_node is not None
    timer_node = dtb.node(board.timer)
    assert timer_node is not None

    i2c_system = Sddf.I2c(sdf, i2c_node, i2c_driver, i2c_virt)
    i2c_system.add_client(client_ds3231)
    i2c_system.add_client(client_pn532)

    timer_system = Sddf.Timer(sdf, timer_node, timer_driver)
    timer_system.add_client(client_pn532)
    timer_system.add_client(client_ds3231)

    pds = [
        timer_driver,
        i2c_driver,
        i2c_virt,
        client_pn532,
        client_ds3231,
    ]
    for pd in pds:
        sdf.add_pd(pd)

    assert i2c_system.connect()
    assert i2c_system.serialise_config(output_dir)
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

    args = parser.parse_args()

    board = next(filter(lambda b: b.name == args.board, BOARDS))

    sdf = SystemDescription(board.arch, board.paddr_top)
    sddf = Sddf(args.sddf)

    with open(args.dtb, "rb") as f:
        dtb = DeviceTree(f.read())

    generate(args.sdf, args.output, dtb)
