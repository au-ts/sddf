# Copyright 2026, UNSW
# SPDX-License-Identifier: BSD-2-Clause

from acacia import (
    System,
    Subsystem,
    ProtectionDomain,
    Channel,
    Map,
    MemoryRegion,
    DTBNode,
    DeviceTreeBlob,
    SchedulingProperties,
    ConfigStruct,
    IRQ,
    SubsystemBuildError,
)
import sys, os
from .driver_manifest import sDDFDriverManifest, sDDFDriverConfig, DTSIRQ, DTSRegion
from .sddf import sDDFDriverClass, DeviceResourcesFactory, RegionResourceFactory
from .i2c import sDDFI2C, I2CAddress
from collections import defaultdict
from typing import List, Dict, Type, Union, Optional


class sDDFPMIC(sDDFDriverClass):
    def __init__(
        self,
        sdf: System,
        dev_compatible: str,
        dev_dt_path: str,
        i2c: sDDFI2C,
        i2c_addr: Optional[I2CAddress] = None,
        driver_prio: int = 254,
        cpu: Optional[int] = None,
        driver_elf: str = "timer_driver.elf",
    ):
        self.i2c = i2c
        assert not i2c.built  # We need to be a client!
        super().__init__(
            sdf, "pmic", dev_compatible, dev_dt_path, magic="sDDF" + chr(1)
        )
        self.driver = ProtectionDomain(
            self.sdf,
            "timer_driver",
            driver_elf,
            scheduling=SchedulingProperties(driver_prio, passive=True),
        )
        self.cpu = cpu

        # PMIC doesn't need device resources (currently)! Just an I2C client for imx.
        # self.driver_dev_resources = self.create_dtb_resources(self.driver)

        # If no address is provided, we should try find one matching our dev_dt_path.
        dtb_i2c_addrs = self.i2c.get_i2c_addresses_from_dtb(self.dtb_node)
        if i2c_addr:
            if i2c_addr not in dtb_i2c_addrs:
                raise ValueError(f"PMIC @ addr={i2c_addr} not present in DTB! Eligible: {dtb_i2c_addrs}")
            self.i2c_addr = i2c_addr
        else:
            if len(dtb_i2c_addrs) != 1:
                # Perhaps we can have better default behaviour?
                raise RuntimeWarning(f"PMIC doesn't have a single I2C address in DTB (found `{dtb_i2c_addrs}`)! Please specify using i2c_addr=(preferred)")
            self.i2c_addr = dtb_i2c_addrs[0] # Should only be one!
        self.client_configs = []

    def connect_clients(self):
        # Clients are connected with:
        # a. channel allowing PPCs -> driver, notifications -> clienet
        # ... that's it!
        for c in self.clients:
            if c.priority > self.driver.priority:
                raise SubsystemBuildError(
                    f"Client {c} has higher priority than timer driver!"
                )
            ch = Channel(
                self.sdf,
                Channel.End(c, can_notify=False, can_pp=True),
                Channel.End(self.driver, can_notify=True, can_pp=False),
            )
            self.client_configs.append(
                self.timer_client_config_factory(c, ch.id_for_pd(c))
            )

    def x86_resources(self):
        self.add_x86_hpet()

    def generate_config_structs(self):
        # We've already made our structs
        return [self.driver_dev_resources] + self.client_configs

    def timer_client_config_factory(
        self, client_pd: ProtectionDomain, driver_id: int
    ) -> ConfigStruct:
        """
        create timer_client_config for client_pd with serial id n
        """
        # invariant: this PD only is a client to timer one time.
        fields = {"magic": "sDDF" + chr(6), "driver_id": driver_id}
        return ConfigStruct(
            "timer_client_config_t",
            target_file=client_pd.prog_image,
            section_name="timer_client_config",
            fields=fields,
        )


# Driver configs
def add_driver_config(driver_name: str, config: sDDFDriverConfig):
    sDDFDriverManifest().add_driver_config(sDDFPMIC, driver_name, config)


# pulp
add_driver_config(
    "apb_timer",
    sDDFDriverConfig(
        compatible="pulp,apb_timer",
        regions=[DTSRegion("regs", "rw", 4096, 0)],
        irqs=[DTSIRQ(0), DTSIRQ(1), DTSIRQ(2), DTSIRQ(3)],
    ),
)
# armv8
add_driver_config(
    "arm", sDDFDriverConfig(compatible="arm,armv8-timer", regions=[], irqs=[DTSIRQ(1)])
)

# bcm2835
add_driver_config(
    "bcm2835",
    sDDFDriverConfig(
        compatible="brcm,bcm2835-system-timer",
        regions=[DTSRegion("regs", dt_idx=0)],
        irqs=[DTSIRQ(1)],
    ),
)

# cdns
add_driver_config(
    "cdns",
    sDDFDriverConfig(
        compatible="cdns,ttc",
        regions=[DTSRegion("regs", dt_idx=0)],
        irqs=[DTSIRQ(0), DTSIRQ(1)],
    ),
)

# goldfish
add_driver_config(
    "goldfish",
    sDDFDriverConfig(
        compatible="google,goldfish-rtc",
        regions=[DTSRegion("regs", dt_idx=0)],
        irqs=[DTSIRQ(0)],
    ),
)

# imx8
add_driver_config(
    "imx",
    sDDFDriverConfig(
        compatible=["fsl,imx8mm-gpt", "fsl,imx8mq-gpt", "fsl,imx8mp-gpt"],
        regions=[DTSRegion("regs", "rw", 65536, 0)],
        irqs=[DTSIRQ(0)],
    ),
)

# jh7110
add_driver_config(
    "jh7110",
    sDDFDriverConfig(
        compatible="starfive,jh7110-timer",
        regions=[DTSRegion("regs", "rw", 4096, 0)],
        irqs=[DTSIRQ(0), DTSIRQ(1)],
    ),
)

# meson_gxbb
add_driver_config(
    "meson",
    sDDFDriverConfig(
        compatible="amlogic,meson-gxbb-wdt",
        regions=[DTSRegion("regs", "rw", 4096, 0)],
        irqs=[DTSIRQ(0)],
    ),
)

# rk3568
add_driver_config(
    "rk3568",
    sDDFDriverConfig(
        compatible="rockchip,rk3568-timer",
        regions=[DTSRegion("regs", dt_idx=0)],
        irqs=[DTSIRQ(0), DTSIRQ(1)],
    ),
)
