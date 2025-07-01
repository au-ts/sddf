# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause
import argparse
from typing import List
from dataclasses import dataclass
from sdfgen import SystemDescription, Sddf, DeviceTree
from importlib.metadata import version

# assert version('sdfgen').split(".")[1] == "24", "Unexpected sdfgen version"

ProtectionDomain = SystemDescription.ProtectionDomain


@dataclass
class Board:
    name: str
    arch: SystemDescription.Arch
    paddr_top: int
    irq_con: str


# @ Tristan: we need to figure out what this means in the device tree
BOARDS: List[Board] = [
    Board(
        name="odroidc4",
        arch=SystemDescription.Arch.AARCH64,
        paddr_top=0x80000000,
        # @Tristan: Right now we can only map one set of MMIO registers in the driver
        # so for now we expose one and hardcode the rest of the mappings
        # gpio="soc/bus@ff600000/bus@34400/pinctrl@40/bank@40",
        # gpio_ao="soc/bus@ff800000/sys-ctrl@0/pinctrl@14/bank@14",
        irq_con="soc/bus@ffd00000/interrupt-controller@f080",
    ),
]


def generate(sdf_file: str, output_dir: str, dtb: DeviceTree):
    gpio_driver = ProtectionDomain("gpio_driver", "gpio_driver.elf", priority=254)
    client = ProtectionDomain("client", "client.elf", priority=1)

    # @Tristan: there are multiple nodes in the DTS we need in the gpio_driver PD
    # so currently we manually add them all
    gpio_mr = MemoryRegion("gpio_mr", 0x1000, paddr=0xff634000)
    gpio_ao_mr = MemoryRegion("gpio_ao_mr", 0x1000, paddr=0xff800000)
    sdf.add_mr(gpio_mr)
    sdf.add_mr(gpio_ao_mr)

    gpio_driver.add_map(Map(gpio_mr, 0x30_000_000, "rw", cached=False))
    gpio_driver.add_map(Map(gpio_ao_mr, 0x30_100_000, "rw", cached=False))

    # @Tristan : I choose to only use the IRQ controller node because it contains Most of the IRQs
    # @ Tristan: DTS doesnt even contain the AO irqs anyway?
    irq_con_node = dtb.node(board.irq_con)
    assert irq_con_node is not None

    gpio_system = Sddf.Gpio(sdf, irq_con_node, gpio_driver)

    # @ Tristan: we want to claim driver ids 0 and 1
    driver_ids = [0, 1]
    gpio_system.add_client(client, driver_ids=driver_ids)

    pds = [
        gpio_driver,
        client
    ]
    for pd in pds:
        sdf.add_pd(pd)

    assert gpio_system.connect()
    assert gpio_system.serialise_config(output_dir)

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
