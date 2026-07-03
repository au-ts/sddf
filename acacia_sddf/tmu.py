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
from collections import defaultdict
from typing import List, Dict, Type, Union, Optional

TMU_PROTOCOL_MAGIC = "TMU" + chr(2)


class sDDFTMU(sDDFDriverClass):
    def __init__(
        self,
        dev_compatible: str,
        dev_dt_path: str,
        sdf: System,
        driver_prio: int,
        cpu: Optional[int] = None,
        driver_elf: str = "tmu_driver.elf",
    ):
        super().__init__("tmu", dev_compatible, dev_dt_path, sdf, magic="sDDF" + chr(1))
        self.driver = ProtectionDomain(
            "tmu_driver",
            driver_elf,
            scheduling=SchedulingProperties(driver_prio, passive=True),
            cpu=cpu,
        )
        self.pds.append(self.driver)
        self.cpu = cpu

        # Create driver resources before doing anything else
        self.driver_dev_resources = self.create_dtb_resources(self.driver)
        self.driver_config = None
        self.client_configs = []
        self.irq_fwd_client = None  # One client may receive forwarded IRQs

    def connect_clients(self):
        # Clients are connected with:
        # a. channel allowing PPCs -> driver, notifications -> clienet
        # ... that's it!
        fwd_channel = None
        for c in self.clients:
            if c.priority > self.driver.priority:
                raise SubsystemBuildError(
                    f"Client {c} has higher priority than tmu driver!"
                )
            do_fwd = c is self.irq_fwd_client
            ch = Channel(
                Channel.End(c, can_notify=do_fwd, can_pp=True),
                Channel.End(self.driver, can_notify=True, can_pp=False),
            )
            if do_fwd:
                fwd_channel = ch
            self.channels.append(ch)
            self.client_configs.append(
                self.tmu_client_config_factory(c, ch.id_for_pd(c))
            )
        # Make driver config
        self.driver_config = self.tmu_driver_config_factory(fwd_channel)

    def add_client(self, client: ProtectionDomain, rcv_forwarded_irq=False):
        if rcv_forwarded_irq:
            if self.irq_fwd_client is not None:
                raise RuntimeError("TMU only supports forwarding IRQs to one client!")
                self.irq_fwd_client = client
        if client not in self.clients:
            self.clients.append(client)

    def generate_config_structs(self):
        # We've already made our structs
        return [self.driver_dev_resources, self.driver_config] + self.client_configs

    def tmu_driver_config_factory(self, irq_fwd_channel: Channel) -> ConfigStruct:
        """
        Create driver config
        """
        # invariant: this PD only is a client to tmu one time.
        fields = {"magic": TMU_PROTOCOL_MAGIC}
        if self.irq_fwd_client:
            fields["irq_fwd_channel"] = irq_fwd_channel.ch_for_pd(self.driver)
            fields["do_irq_fwd"] = True
        else:
            fields["irq_fwd_channel"] = 0
            fields["do_irq_fwd"] = False
        return ConfigStruct(
            "tmu_driver_config_t",
            target_file=self.driver.prog_image,
            section_name="tmu_driver_config",
            fields=fields,
        )

    def tmu_client_config_factory(
        self, client_pd: ProtectionDomain, driver_id: int
    ) -> ConfigStruct:
        """
        create tmu_client_config for client_pd
        """
        # invariant: this PD only is a client to tmu one time.
        fields = {"magic": TMU_PROTOCOL_MAGIC, "driver_id": driver_id}
        return ConfigStruct(
            "tmu_client_config_t",
            target_file=client_pd.prog_image,
            section_name="tmu_client_config",
            fields=fields,
        )


# Driver configs
def add_driver_config(driver_name: str, config: sDDFDriverConfig):
    sDDFDriverManifest().add_driver_config(sDDFTMU, driver_name, config)


# imx
add_driver_config(
    "imx",
    sDDFDriverConfig("fsl,imx8mq-tmu", [DTSRegion("regs", dt_idx=0)], [DTSIRQ(0)]),
)
