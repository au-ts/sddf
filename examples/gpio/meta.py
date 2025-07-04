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


# @ Tristan: we need to figure out what this meansn the device tree
BOARDS: List[Board] = [
    Board(
        name="odroidc4",
        arch=SystemDescription.Arch.AARCH64,
        paddr_top=0x80000000,
        # @Tristan: Right now we can only map one set of MMIO registers in the driver
        # so for now we expose one and hardcode the rest of the mappings

        # so in meson drivers there is no GPIO node in the DTS so you have to go through pinctrl
        # the pinctrl driver is both the pinmux and gpio controller ( :( )
        gpio="soc/bus@ff600000/bus@34400/pinctrl@40",

        # This node has no compatiblie string
        # but it contains all of the registers still
        # gpio="soc/bus@ff600000/bus@34400/pinctrl@40/bank@40",

        # This is the AO bank which has the same problem as above
        # # NOTE: this is not compatible either with amlogic,meson-g12a-periphs-pinctrl
        # must be amlogic,meson-g12a-aobus-pinctrl
        # gpio="soc/bus@ff800000/sys-ctrl@0/pinctrl@14" 
        # gpio="soc/bus@ff800000/sys-ctrl@0/pinctrl@14/bank@14",

        # This is for the int-cont MMIO reg and also all the interrupts  
        # irq_con="soc/bus@ffd00000/interrupt-controller@f080",
    ),
     Board(
        name="maaxboard",
        arch=SystemDescription.Arch.AARCH64,
        paddr_top=0x7_0000_000,
        gpio="soc@0/bus@30000000/gpio@30200000",
        # gpio="soc@0/bus@30000000/gpio@30210000", # these are also compatible as well
        # gpio="soc@0/bus@30000000/gpio@30220000",
        # gpio="soc@0/bus@30000000/gpio@30230000",
        # gpio="soc@0/bus@30000000/gpio@30240000"
    )

]

def generate(sdf_file: str, output_dir: str, dtb: DeviceTree):
    gpio_driver = ProtectionDomain("gpio_driver", "gpio_driver.elf", priority=254)
    client = ProtectionDomain("client", "client.elf", priority=1)

    if board.name == "odroidc4":
        # @Tristan: so there is an extra int-cont node for meson drivers that we will hardcode
        # into the gpio driver for now, in the future this should be an xtra PD

        # we need to add the IRQs and the regs here from the int controller
        # the DTS has all the interrupts listed so we should harcode all of them?
        # for now the driver - device channels are fixed
        gpio_driver.add_irq(Irq(97, Irq.Trigger.EDGE, 54))
        gpio_driver.add_irq(Irq(98, Irq.Trigger.EDGE, 55)) 
        gpio_driver.add_irq(Irq(99, Irq.Trigger.EDGE, 56)) 
        gpio_driver.add_irq(Irq(100, Irq.Trigger.EDGE, 57)) 
        gpio_driver.add_irq(Irq(101, Irq.Trigger.EDGE, 58)) 
        gpio_driver.add_irq(Irq(102, Irq.Trigger.EDGE, 59)) 
        gpio_driver.add_irq(Irq(103, Irq.Trigger.EDGE, 60)) 
        gpio_driver.add_irq(Irq(104, Irq.Trigger.EDGE, 61)) 

        # There is GPIO_AO interupts as well (ao_irq_0 and ao_irq_1) but theres no node in the DTS for it
        # This is because they dont feed into the A55 GIC and they go into the SCP (the Always-On processor) instead

        # So remember from before the pinctrl node doesnt have the register ranges so we have to hardcode
        # whichever bank we choose
        gpio_mr = MemoryRegion(sdf, "gpio_mr", 0x1000, paddr=0xff634000)
        # gpio_ao_mr = MemoryRegion(sdf, "gpio_ao_mr", 0x1000, paddr=0xff800000)
        sdf.add_mr(gpio_mr)
        # sdf.add_mr(gpio_ao_mr)

        gpio_driver.add_map(Map(gpio_mr, 0x30_000_000, "rw", cached=False))
        # gpio_driver.add_map(Map(gpio_ao_mr, 0x30_000_000, "rw", cached=False))

        # soc/bus@ffd00000/interrupt-controller@f080 is not page aligned
        irq_con_mr = MemoryRegion(sdf, "irq_con", 0x1000, paddr=0xffd0f000)
        sdf.add_mr(irq_con_mr)
        gpio_driver.add_map(Map(irq_con_mr, 0x30_100_000, "rw", cached=False)) 

        # the config.json should also look like this
        # "resources": {
        #     "regions": [],
        #     "irqs": []
        # }

    # else:
        # For IMX it everything is normal and how you would expect
        # im currently hardcoding the channel ids for device irqs
        # TODO: maybe we shoudl figure out what to do in terms of hardcoding these values in the config.json
        # and thus the driver? we need this to match up with the gpio_config.h file as well

    gpio_node = dtb.node(board.gpio)
    assert gpio_node is not None

    gpio_system = Sddf.Gpio(sdf, gpio_node, gpio_driver)

    # @ Tristan: we want to claim driver channel ids 0 and 1
    driver_channel_ids = [0, 1]
    gpio_system.add_client(client, driver_channel_ids=driver_channel_ids)

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
