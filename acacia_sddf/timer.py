# Copyright 2026, UNSW
# SPDX-License-Identifier: BSD-2-Clause

from acacia import System, Subsystem, ProtectionDomain, Channel, Map, MemoryRegion, DTBNode, DeviceTreeBlob, SchedulingProperties, ConfigStruct, IRQ, SubsystemBuildError
import sys, os
from .driver_manifest import sDDFDriverManifest, sDDFDriverConfig, DTSIRQ, DTSRegion
from .sddf import sDDFDriverClass, DeviceResourcesFactory, RegionResourceFactory
from collections import defaultdict
from typing import List, Dict, Type, Union, Optional

class sDDFTimer(sDDFDriverClass):
    def __init__(self,
                 dev_compatible: str,
                 dev_dt_path: str,
                 sdf: System,
                 driver_prio: int=254,
                 cpu:Optional[int]=None,
                 driver_elf: str="timer_driver.elf"
                 ):
        super().__init__("timer", dev_compatible, dev_dt_path, sdf, magic="sDDF"+chr(1))
        self.driver = ProtectionDomain("timer_driver", driver_elf, scheduling=SchedulingProperties(driver_prio, passive=True))
        self.pds.append(self.driver)
        self.cpu = cpu

        # Create driver resources before doing anything else
        self.driver_dev_resources = self.create_dtb_resources(self.driver)
        self.client_configs = []

    def connect_clients(self):
        # Clients are connected with:
        # a. channel allowing PPCs -> driver, notifications -> clienet
        # ... that's it!
        for c in self.clients:
            if c.priority > self.driver.priority:
                raise SubsystemBuildError(f"Client {c} has higher priority than timer driver!")
            ch = Channel(
                    Channel.End(c, can_notify=False, can_pp=True),
                    Channel.End(self.driver, can_notify=True, can_pp=False)
            )
            self.channels.append(ch)
            self.client_configs.append(
                self.timer_client_config_factory(c, ch.id_for_pd(c))
            )

    def generate_config_structs(self):
        # We've already made our structs
        return [self.driver_dev_resources] + self.client_configs

    def timer_client_config_factory(self, client_pd: ProtectionDomain, driver_id: int) -> ConfigStruct:
        """
        create timer_client_config for client_pd with serial id n
        """
        # invariant: this PD only is a client to timer one time.
        fields = {
            "magic": "sDDF"+chr(6),
            "driver_id": driver_id
        }
        return ConfigStruct("timer_client_config_t", target_file=client_pd.prog_image, section_name="timer_client_config", fields=fields)


    # x86 utility
    # NOTE: is this safe to call automatically? I currently am assuming we want manual
    # control over this since we didn't bake it into sdfgen before.
    def add_x86_hpet(self, sdf: System):
        # Timer IRQ must be the highest priority (highest vector) to ensure they are delivered
        # as close as possible to the timer expiry. The highest vector is defined by (irq_user_max - irq_user_min) in seL4 source
        # Since our HPET driver uses legacy IRQ routing, comparator 0's IRQ will always arrives at
        # I/O APIC 0's pin 2.
        from acacia.irq import IrqIoapic
        hpet_irq = IrqIoapic(
            ioapic_id=0,
            pin=2,
            vector=107,
            id=0,
            trigger=IRQ.Trigger.EDGE
        )
        self.driver.add_irq(hpet_irq)
        # paddr=0xFED00000 is a x86 convention for HPET, though it may be different on some machines depending on their BIOS.
        hpet_regs = MemoryRegion(
            "hpet_regs", 0x1000, paddr=0xFED00000
        )
        hpet_regs_map = Map(hpet_regs, 0x5000_0000, "rw")
        self.driver.add_map(hpet_regs_map)
        sdf.add_memory_region(hpet_regs)

# Driver configs
def add_driver_config(driver_name: str, config: sDDFDriverConfig):
    sDDFDriverManifest().add_driver_config(sDDFTimer, driver_name, config)

# pulp
add_driver_config(
    "apb_timer",
    sDDFDriverConfig(
        compatible="pulp,apb_timer",
        regions=[DTSRegion("regs", "rw", 4096, 0)],
        irqs=[DTSIRQ(0), DTSIRQ(1), DTSIRQ(2), DTSIRQ(3)]
    )
)
# armv8
add_driver_config(
    "arm",
    sDDFDriverConfig(
        compatible="arm,armv8-timer",
        regions=[],
        irqs=[DTSIRQ(1)]
    )
)

# bcm2835
add_driver_config(
    "bcm2835",
    sDDFDriverConfig(
        compatible="brcm,bcm2835-system-timer",
        regions=[DTSRegion("regs", dt_idx=0)],
        irqs=[DTSIRQ(1)]
    )
)

# cdns
add_driver_config(
    "cdns",
    sDDFDriverConfig(
        compatible="cdns,ttc",
        regions=[DTSRegion("regs", dt_idx=0)],
        irqs=[DTSIRQ(0), DTSIRQ(1)]
    )
)

# goldfish
add_driver_config(
    "goldfish",
    sDDFDriverConfig(
        compatible="google,goldfish-rtc",
        regions=[DTSRegion("regs", dt_idx=0)],
        irqs=[DTSIRQ(0)]
    )
)

# imx8
add_driver_config(
    "imx",
    sDDFDriverConfig(
        compatible=["fsl,imx8mm-gpt", "fsl,imx8mq-gpt", "fsl,imx8mp-gpt"],
        regions=[DTSRegion("regs", "rw", 65536, 0)],
        irqs=[DTSIRQ(0)]
    )
)

# jh7110
add_driver_config(
    "jh7110",
    sDDFDriverConfig(
        compatible="starfive,jh7110-timer",
        regions=[DTSRegion("regs", "rw", 4096, 0)],
        irqs=[DTSIRQ(0), DTSIRQ(1)]
    )
)

# meson_gxbb
add_driver_config(
    "meson",
    sDDFDriverConfig(
        compatible="amlogic,meson-gxbb-wdt",
        regions=[DTSRegion("regs", "rw", 4096, 0)],
        irqs=[DTSIRQ(0)]
    )
)

# rk3568
add_driver_config(
    "rk3568",
    sDDFDriverConfig(
        compatible="rockchip,rk3568-timer",
        regions=[DTSRegion("regs", dt_idx=0)],
        irqs=[DTSIRQ(0), DTSIRQ(1)]
    )
)

