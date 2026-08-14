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
        driver_prio: Optional[int] = None,
        cpu: Optional[int] = None,
        driver_elf: str = "pmic_driver.elf",
    ):
        self.i2c = i2c
        self.cpu = cpu
        assert not i2c.built  # We need to be a client!
        super().__init__(
            sdf, "pmic", dev_compatible, dev_dt_path, magic="sDDF" + chr(1)
        )
        if driver_prio:
            assert driver_prio < i2c.virt.priority
        else:
            # Default to just below i2c virt
            driver_prio = i2c.virt.priority - 1
        self.driver = ProtectionDomain(
            self.sdf,
            "pmic_driver",
            driver_elf,
            scheduling=SchedulingProperties(driver_prio),
            cpu=self.cpu,
        )
        i2c.add_client(self.driver)

        # PMIC doesn't need device resources (currently)! Just an I2C client for imx.
        # self.driver_dev_resources = self.create_dtb_resources(self.driver)

        # If no address is provided, we should try find one matching our dev_dt_path.
        dtb_i2c_addrs = self.i2c.get_i2c_addresses_from_dtb(self.dtb_node)
        if i2c_addr:
            if i2c_addr not in dtb_i2c_addrs:
                raise ValueError(
                    f"PMIC @ addr={i2c_addr} not present in DTB! Eligible: {dtb_i2c_addrs}"
                )
            self.i2c_addr = i2c_addr
        else:
            if len(dtb_i2c_addrs) != 1:
                # Perhaps we can have better default behaviour?
                raise RuntimeWarning(
                    f"PMIC doesn't have a single I2C address in DTB (found `{dtb_i2c_addrs}`)! Please specify using i2c_addr=(preferred)"
                )
            self.i2c_addr = dtb_i2c_addrs[0]  # Should only be one!

        if self.i2c_addr.is_ten_bit:
            raise RuntimeError(
                "The sDDF does not currently support ten-bit I2C addresses!"
            )

        # TODO: claim i2c address from i2c driver once support is added to do so
        self.client_configs = []

    def connect_clients(self):
        # Clients are connected with:
        # a. channel allowing PPCs -> driver
        for c in self.clients:
            if c.priority > self.driver.priority:
                raise SubsystemBuildError(
                    f"Client {c} has higher priority than pmic driver!"
                )
            ch = Channel(
                self.sdf,
                Channel.End(c, can_notify=False, can_pp=True),
                Channel.End(self.driver, can_notify=False, can_pp=False),
            )
            self.client_configs.append(
                self.pmic_client_config_factory(c, ch.id_for_pd(c))
            )

    def x86_resources(self):
        self.add_x86_hpet()

    def generate_config_structs(self):
        # We've already made our structs
        return [self.pmic_driver_config_factory()] + self.client_configs

    def pmic_driver_config_factory(self) -> ConfigStruct:
        """
        create pmic_driver_config_t for driver.
        """
        fields = {"magic": "sDDF" + chr(7), "i2c_addr": self.i2c_addr.addr}
        return ConfigStruct(
            "pmic_driver_config_t",
            target_file=self.driver.prog_image,
            section_name="pmic_driver_config",
            fields=fields,
        )

    def pmic_client_config_factory(
        self, client_pd: ProtectionDomain, driver_id: int
    ) -> ConfigStruct:
        """
        create pmic_client_config for client_pd
        """
        # invariant: this PD only is a client to pmic one time.
        fields = {"magic": "sDDF" + chr(7), "driver_id": driver_id}
        return ConfigStruct(
            "pmic_client_config_t",
            target_file=client_pd.prog_image,
            section_name="pmic_client_config",
            fields=fields,
        )


# Driver configs
def add_driver_config(driver_name: str, config: sDDFDriverConfig):
    sDDFDriverManifest().add_driver_config(sDDFPMIC, driver_name, config)


# imx
add_driver_config(
    "bd71837",
    sDDFDriverConfig(
        "rohm,bd71837",
        regions=[],
        irqs=[],
    ),
)
