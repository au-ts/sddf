# Copyright 2026, UNSW
# SPDX-License-Identifier: BSD-2-Clause

from typing import Optional

from acacia import (
    IRQ,
    Channel,
    ConfigStruct,
    Map,
    MemoryRegion,
    ProtectionDomain,
    SchedulingProperties,
    SubsystemBuildError,
    System,
)

from .driver_manifest import register_sddf_subsystem
from .sddf import sDDFDriverClass

TIMER_PROTOCOL_MAGIC = "sDDF" + chr(6)


class sDDFTimer(sDDFDriverClass):
    def __init__(
        self,
        sdf: System,
        dev_compatible: str,
        dev_dt_path: str,
        driver_prio: int = 254,
        cpu: Optional[int] = None,
        driver_elf: str = "timer_driver.elf",
    ):
        self.cpu = cpu
        driver = ProtectionDomain(
            sdf,
            "timer_driver",
            driver_elf,
            scheduling=SchedulingProperties(driver_prio, passive=True),
            cpu=self.cpu,
        )
        super().__init__(
            sdf, driver, "timer", dev_compatible, dev_dt_path, magic="sDDF" + chr(1)
        )

        self.client_configs = []

    def connect_clients(self):
        # Clients are connected with:
        # a. channel allowing PPCs -> driver, notifications -> client
        # ... that's it!
        for c in self.clients:
            if c.priority >= self.driver.priority:
                raise SubsystemBuildError(
                    f"Client {c} has higher or equal priority to timer driver!"
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
        return super().generate_config_structs() + self.client_configs

    def timer_client_config_factory(
        self, client_pd: ProtectionDomain, driver_id: int
    ) -> ConfigStruct:
        """
        create timer_client_config for client_pd with serial id n
        """
        # invariant: this PD only is a client to timer one time.
        fields = {"magic": TIMER_PROTOCOL_MAGIC, "driver_id": driver_id}
        return ConfigStruct(
            fields,
            type_name="timer_client_config_t",
            target_file=client_pd.prog_image,
            section_name="timer_client_config",
        )

    # x86 utility
    def add_x86_hpet(self):
        # Timer IRQ must be the highest priority (highest vector) to ensure they are delivered
        # as close as possible to the timer expiry. The highest vector is defined by (irq_user_max - irq_user_min) in seL4 source
        # Since our HPET driver uses legacy IRQ routing, comparator 0's IRQ will always arrives at
        # I/O APIC 0's pin 2.
        from acacia.irq import IrqIoapic

        hpet_irq = IrqIoapic(
            ioapic_id=0, pin=2, vector=107, id=0, trigger=IRQ.Trigger.EDGE
        )
        self.driver.add_irq(hpet_irq)
        # paddr=0xFED00000 is a x86 convention for HPET, though it may be different on some machines depending on their BIOS.
        hpet_regs = MemoryRegion(
            self.sdf, "hpet_regs", 0x1000, paddr=0xFED00000, cached=False
        )
        hpet_regs_map = Map(hpet_regs, 0x5000_0000, "rw")
        self.driver.add_map(hpet_regs_map)


# Tell driver manifest we exist and that drivers in the timer tree are usable for us.
register_sddf_subsystem("timer", sDDFTimer)
