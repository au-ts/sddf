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
    build_hook,
)
import sys, os
from .driver_manifest import (
    register_sddf_subsystem,
    sDDFDriverManifest,
    sDDFDriverConfig,
    DTSIRQ,
    DTSRegion,
)
from .sddf import sDDFDriverClass, DeviceResourcesFactory, RegionResourceFactory
from collections import defaultdict
from typing import List, Dict, Type, Union, Optional

TMU_PROTOCOL_MAGIC = "TMU" + chr(2)


class sDDFTMU(sDDFDriverClass):
    def __init__(
        self,
        sdf: System,
        dev_compatible: str,
        dev_dt_path: str,
        driver_prio: int,
        cpu: Optional[int] = None,
        allow_irq_fwd: bool = True,
        driver_elf: str = "tmu_driver.elf",
    ):
        driver = ProtectionDomain(
            sdf,
            "tmu_driver",
            driver_elf,
            scheduling=SchedulingProperties(driver_prio, passive=True),
            cpu=cpu,
        )
        self.cpu = cpu
        super().__init__(
            sdf, driver, "tmu", dev_compatible, dev_dt_path, magic="sDDF" + chr(1)
        )

        # Empty config listings
        self.driver_config = None
        self.client_configs = []
        self.controller_client = None  # One client may receive forwarded IRQs

    @build_hook
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
            do_fwd = c is self.controller_client
            ch = Channel(
                self.sdf,
                Channel.End(c, can_notify=do_fwd, can_pp=True),
                Channel.End(self.driver, can_notify=True, can_pp=False),
            )
            if do_fwd:
                fwd_channel = ch
            self.client_configs.append(
                self.tmu_client_config_factory(c, ch.id_for_pd(c))
            )
        # Make driver config
        self.driver_config = self.tmu_driver_config_factory(fwd_channel)

    def add_client(self, client: ProtectionDomain, is_controller=False):
        if is_controller:
            if self.controller_client is not None:
                raise RuntimeError("TMU only supports forwarding IRQs to one client!")
                self.controller_client = client
        if client not in self.clients:
            self.clients.append(client)

    def generate_config_structs(self):
        # We've already made our structs
        return (
            super().generate_config_structs()
            + [self.driver_config]
            + self.client_configs
        )

    def tmu_driver_config_factory(self, controller_channel: Channel) -> ConfigStruct:
        """
        Create driver config
        """
        # invariant: this PD only is a client to tmu one time.
        fields = {"magic": TMU_PROTOCOL_MAGIC}
        if self.controller_client:
            fields["controller_channel"] = controller_channel.ch_for_pd(self.driver)
            fields["do_irq_fwd"] = True
        else:
            fields["controller_channel"] = 0
            fields["do_irq_fwd"] = False
        return ConfigStruct(
            fields,
            "tmu_driver_config_t",
            target_file=self.driver.prog_image,
            section_name="tmu_driver_config",
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
            fields,
            "tmu_client_config_t",
            target_file=client_pd.prog_image,
            section_name="tmu_client_config",
        )


# Tell driver manifest we exist and that drivers in the serial tree are usable for us.
register_sddf_subsystem("tmu", sDDFTMU)
