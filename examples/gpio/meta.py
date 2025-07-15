# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause
import argparse
from typing import List
from dataclasses import dataclass
from sdfgen import SystemDescription, Sddf, DeviceTree
from importlib.metadata import version

# assert version('sdfgen').split(".")[1] == "24", "Unexpected sdfgen version"

ProtectionDomain = SystemDescription.ProtectionDomain
Irq = SystemDescription.Irq
MemoryRegion = SystemDescription.MemoryRegion
Map = SystemDescription.Map

@dataclass
class Board:
    name: str
    arch: SystemDescription.Arch
    paddr_top: int
    gpio: str


BOARDS: List[Board] = [
    Board(
        name="odroidc4",
        arch=SystemDescription.Arch.AARCH64,
        paddr_top=0x80000000,
        gpio="soc/bus@ff600000/bus@34400/pinctrl@40",
        # Right now we can only mpa one DTS node in driver
        # so we currently has hardcode the rest of the mappings

        # For the MESON GPIO driver there are a lot of weird things going on.

        # There are 5 nodes we consider mapping
        # 1. gpio="soc/bus@ff600000/bus@34400/pinctrl@40",
        #   - This is the pinctrl node for peripheral bank
        #   - It has a compatibilty string (a requirement)
        #   - This is it "amlogic,meson-g12a-periphs-pinctrl"
        #   - DOESN't contain any memory regions or interrupts though
        #
        # 2. gpio="soc/bus@ff600000/bus@34400/pinctrl@40/bank@40",
        #   - Doesn't contain a compatibilty string so we cant map it
        #   - Contains all the mapped memory regions for the peripheral GPIO bank 
        #
        # 3.  gpio="soc/bus@ff800000/sys-ctrl@0/pinctrl@14" 
        #   - This is the pinctrl node for AO bank.
        #   - It has a compatibilty string (a requirement)
        #   - This is it "amlogic,meson-g12a-aobus-pinctrl"
        #   - Probably not even useful as none of the pins are brought out
        #
        # 4. gpio="soc/bus@ff800000/sys-ctrl@0/pinctrl@14/bank@14",
        #   - Doesn't contain a compatibilty string so we cant map it 
        #   - Contains all the mapped memory regions for the AO GPIO bank 
        #
        # 5. irq_con="soc/bus@ffd00000/interrupt-controller@f080"
        #   - This is the interrupt controller node for ALL GPIO pins (AO and peripheral)
        #   - It muxes the pins into the specific interrupt lines
        #   - Contains mapped memory regions and all the interrupts
        #   - The interrupts it contains are marked like this
        #   - amlogic,channel-interrupts = <0x40 0x41 0x42 0x43 0x44 0x45 0x46 0x47>;
        #   - so the dtb library cannot even parse it
        #   - To clarify both the other bank would need to access this irq_con's registers
        #

        # Therefore:
        # I think we have 2 options
        # 
        # 1. We use gpio="soc/bus@ff600000/bus@34400/pinctrl@40" and hardcode the interrupt controller
        # Remember that gpio AO banks have no pins brought out anyway (so its useless??)
        # 
        # 2. We need to make a seperate interrupt controller driver that takes the DTS node for it
        # Than both gpio="soc/bus@ff600000/bus@34400/pinctrl@40" and gpio="soc/bus@ff800000/sys-ctrl@0/pinctrl@14" PD's
        # Communicate with it (i think this wont be very hard)
        #

        # NOTE: the 2 banks have different compatiblity strings as well but the implementation for both
        # should be almost identical 
    ),
     Board(
        name="maaxboard",
        arch=SystemDescription.Arch.AARCH64,
        paddr_top=0x7_0000_000,
        gpio="soc@0/bus@30000000/gpio@30200000",
    )

]

def generate(sdf_file: str, output_dir: str, dtb: DeviceTree):
    gpio_driver = ProtectionDomain("gpio_driver", "gpio_driver.elf", priority=254)
    client = ProtectionDomain("client", "client.elf", priority=1)

    if board.name == "odroidc4":
        # Hardcode the register ranges because pinctrl node doesn't have any
        gpio_mr = MemoryRegion(sdf, "gpio_mr", 0x1000, paddr=0xff634000)
        sdf.add_mr(gpio_mr)
        gpio_driver.add_map(Map(gpio_mr, 0x30_000_000, "rw", cached=False))

        # gpio_ao_mr = MemoryRegion(sdf, "gpio_ao_mr", 0x1000, paddr=0xff800000)
        # sdf.add_mr(gpio_ao_mr)
        # gpio_driver.add_map(Map(gpio_ao_mr, 0x30_000_000, "rw", cached=False))

        # Hardcode the interrupt controller register ranges
        # soc/bus@ffd00000/interrupt-controller@f080 is not page aligned
        irq_con_mr = MemoryRegion(sdf, "irq_con", 0x1000, paddr=0xffd0f000)
        sdf.add_mr(irq_con_mr)
        gpio_driver.add_map(Map(irq_con_mr, 0x30_100_000, "rw", cached=False)) 

        # We fix the device irq channels at the end 54 - 61
        # This would need to match up with a protocol in gpio_config.h
        # and the driver
        gpio_driver.add_irq(Irq(97, Irq.Trigger.EDGE, 54))
        gpio_driver.add_irq(Irq(98, Irq.Trigger.EDGE, 55)) 
        gpio_driver.add_irq(Irq(99, Irq.Trigger.EDGE, 56)) 
        gpio_driver.add_irq(Irq(100, Irq.Trigger.EDGE, 57)) 
        gpio_driver.add_irq(Irq(101, Irq.Trigger.EDGE, 58)) 
        gpio_driver.add_irq(Irq(102, Irq.Trigger.EDGE, 59)) 
        gpio_driver.add_irq(Irq(103, Irq.Trigger.EDGE, 60)) 
        gpio_driver.add_irq(Irq(104, Irq.Trigger.EDGE, 61)) 

        # There is GPIO_AO interupts as well (ao_irq_0 and ao_irq_1) but theres no node in the DTS for it
        # This is because they dont feed into the A55 GIC and they go into the SCP (the Always-On processor)

        # NOTE: since we hardcode everything the config.json should also look like this
        # "resources": {
        #     "regions": [],
        #     "irqs": []
        # }

        # NOTE: from my research i can only find 3 DTS nodes in Linux
        # that use a seperate interrupt controller
        # - amlogic,meson-gpio-intc
        # - st,stm32-exti
        # - fsl,ls-extirq

    # else:
        # IMX and most other GPIO's have no issues

    gpio_node = dtb.node(board.gpio)
    assert gpio_node is not None

    gpio_system = Sddf.Gpio(sdf, gpio_node, gpio_driver)

    # These need to be different to the ones hardcoded in config.json or this file
    driver_channel_ids = [0, 1, 3]
    gpio_system.add_client(client, driver_channel_ids=driver_channel_ids)

    pds = [
        gpio_driver,
        client
    ]
    for pd in pds:
        sdf.add_pd(pd)

    # TODO: currently there is no check to see if driver_channel_ids hasn't chosen a channel used
    # by a device irq
    # But it will still fail really deep inside of gpio_system.connect() and not compile

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
