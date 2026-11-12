# Copyright 2026, UNSW
# SPDX-License-Identifier: BSD-2-Clause

from typing import Optional

from acacia.pd import MAX_IDS

from acacia import (
    IRQ,
    build_hook,
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
        if dev_compatible not in ("google,goldfish-rtc", "pulp,apb_timer"):
            raise SubsystemBuildError("Timer virt currently supports Goldfish and CVA6/APB timers")
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
        self.client_config_symbols = {}
        self.virt = ProtectionDomain(
            sdf, "timer_virt", "timer_virt.elf", priority=driver_prio - 1, cpu=cpu
        )
        self.virt_config = ConfigStruct(
            {
                "magic": TIMER_PROTOCOL_MAGIC,
                "driver_id": 0,
                "req_vaddrs" : [0] * MAX_IDS
            },
            type_name="sddf_timer_virt_config_t"
        )
        self.virt_config.make_prefill(self.virt, "timer_config")

    def add_client(self, client: ProtectionDomain, config_symbol: str = "timer_config"):
        super().add_client(client)
        self.client_config_symbols[client] = config_symbol

    @build_hook  # Mark this to run when Acacia is performing final steps
    def connect_clients(self):
        if len(self.clients) >= MAX_IDS:
            raise SubsystemBuildError(f"Timer virt supports at most {MAX_IDS - 1} clients")
        ch = Channel(self.sdf,
                     Channel.End(self.virt, can_notify=False, can_pp=True),
                     Channel.End(self.driver)
            )
        self.virt_config.fields["driver_id"] = ch.id_for_pd(self.virt)
        self.driver_config = ConfigStruct({
                "magic": TIMER_PROTOCOL_MAGIC,
                "virt_id": ch.id_for_pd(self.driver)
            },
            type_name="timer_driver_config_t"
        )
        self.driver_config.make_prefill(self.driver, "config")
        for client in self.clients:
            ch = Channel(self.sdf, Channel.End(client), Channel.End(self.virt))
            mailbox = MemoryRegion(self.sdf, f"timer/{client.name}/requst", 0x1000, physical=True)
            client_map = client.create_automap(mailbox, "rw")
            virt_map = self.virt.create_automap(mailbox, "rw")
            self.client_configs.append(self.timer_client_config_factory(
                client, ch.id_for_pd(client), client_map.vaddr))
            self.virt_config.fields["req_vaddrs"][ch.id_for_pd(self.virt)] = virt_map.vaddr

    def x86_resources(self):
        self.add_x86_hpet()

    def generate_config_structs(self):
        # We've already made our structs
        return super().generate_config_structs() + self.client_configs + [self.virt_config, self.driver_config]

    def timer_client_config_factory(
        self, client_pd: ProtectionDomain, virt_id: int, req_vaddr: int
    ) -> ConfigStruct:
        """
        create timer_client_config for client_pd with serial id n
        """
        # invariant: this PD only is a client to timer one time.
        fields = {"magic": TIMER_PROTOCOL_MAGIC, "virt_id": virt_id, "req_vaddr": req_vaddr}
        config = ConfigStruct(
            fields,
            type_name="timer_client_config_t",
        )
        config.make_prefill(client_pd, self.client_config_symbols[client_pd])
        return config

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
