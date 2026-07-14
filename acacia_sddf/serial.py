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
    SubsystemBuildError,
)
from acacia.x86 import IOPort
from acacia.irq import IrqIoapic
import sys, os
from .driver_manifest import sDDFDriverManifest, sDDFDriverConfig, DTSIRQ, DTSRegion
from .sddf import sDDFDriverClass, DeviceResourcesFactory, RegionResourceFactory
from collections import defaultdict
from typing import List, Dict, Type, Union, Optional

SERIAL_DEFAULT_BEGIN_STR = "Begin input\r\n"
SERIAL_MAX_BEGIN_STR_LEN = 128
SERIAL_PROTOCOL_MAGIC = "sDDF" + chr(0x3)


class sDDFSerial(sDDFDriverClass):
    def __init__(
        self,
        sdf: System,
        dev_compatible: str,
        dev_dt_path: str,
        driver_prio: int,
        virt_tx_prio: int,
        allow_rx: bool = False,
        virt_rx_prio: Optional[int] = None,
        cpu: Optional[int] = None,
        enable_color: bool = True,
        baud_rate: int = 115200,
        begin_str: str = SERIAL_DEFAULT_BEGIN_STR,
        # We leave this as configurable just in case...
        data_size: int = 0x10000,
        queue_size: int = 0x1000,
        virt_rx_elf: str = "serial_virt_rx.elf",
        virt_tx_elf: str = "serial_virt_tx.elf",
        driver_elf: str = "serial_driver.elf",
    ):
        super().__init__(
            sdf, "serial", dev_compatible, dev_dt_path, magic="sDDF" + chr(0x1)
        )
        assert driver_prio > virt_tx_prio > 0
        if allow_rx:
            # Default RX prio == TX prio
            if virt_rx_prio is None:
                virt_rx_prio = virt_tx_prio
            assert driver_prio > virt_rx_prio > 0

        self.cpu = cpu
        self.allow_rx = allow_rx
        self.data_size = data_size
        self.queue_size = queue_size
        self.enable_color = enable_color
        self.baud_rate = baud_rate
        if len(begin_str) > SERIAL_MAX_BEGIN_STR_LEN:
            raise SubsystemBuildError(
                f"begin_str length {len(begin_str)} exceeds max {SERIAL_MAX_BEGIN_STR_LEN}"
            )
        self.begin_str = begin_str

        self.virt_tx = None
        self.virt_rx = None
        self.virt_rx_elf = virt_rx_elf
        self.virt_tx_elf = virt_tx_elf
        self.driver = ProtectionDomain(
            self.sdf,
            "serial_driver",
            driver_elf,
            scheduling=SchedulingProperties(driver_prio),
            cpu=self.cpu,
        )

        # We must make the driver BEFORE we get here
        self.driver_dev_resources = self.create_dtb_resources(self.driver)

        # Stubs of config structs that we need to collect in construct_infrastructure and connect_clients
        self.virt_tx_config = None
        self.virt_rx_config = None
        self.driver_config = None
        self.virt_tx_driver_conn = None
        self.virt_rx_driver_conn = None
        self.client_configs = []
        self.construct_infrastructure(
            virt_rx_prio if virt_rx_prio else -1, virt_tx_prio
        )

    def construct_infrastructure(self, virt_rx_prio: int, virt_tx_prio: int):
        self.virt_tx = ProtectionDomain(
            self.sdf,
            "serial_virt_tx",
            self.virt_tx_elf,
            scheduling=SchedulingProperties(virt_tx_prio),
            cpu=self.cpu,
        )
        if self.allow_rx and virt_rx_prio > 0:
            self.virt_rx = ProtectionDomain(
                self.sdf,
                "serial_virt_rx",
                self.virt_rx_elf,
                scheduling=SchedulingProperties(virt_rx_prio),
                cpu=self.cpu,
            )

        driver_tx_queue_mr = MemoryRegion(
            self.sdf, "serial_driver_tx_queue", self.queue_size
        )
        driver_tx_data_mr = MemoryRegion(
            self.sdf,
            "serial_driver_tx_data",
            self.data_size * 2 if self.enable_color else self.data_size,
            cached=True,
        )

        driver_tx_queue_map = self.driver.create_automap(
            driver_tx_queue_mr, Map.Permissions(r=True, w=True)
        )
        driver_tx_data_map = self.driver.create_automap(
            driver_tx_data_mr, Map.Permissions(r=True, w=True)
        )
        virt_tx_queue_map = self.virt_tx.create_automap(
            driver_tx_queue_mr, Map.Permissions(r=True, w=True)
        )
        virt_tx_data_map = self.virt_tx.create_automap(
            driver_tx_data_mr, Map.Permissions(r=True, w=True)
        )

        driver_virt_tx_ch = Channel(
            self.sdf,
            Channel.End(self.driver, can_notify=True, can_pp=False),
            Channel.End(self.virt_tx, can_notify=True, can_pp=False),
        )

        driver_tx_conn = self.serial_connection_resource_factory(
            driver_tx_queue_map,
            driver_tx_data_map,
            driver_virt_tx_ch.id_for_pd(self.driver),
        )
        self.virt_tx_driver_conn = self.serial_connection_resource_factory(
            virt_tx_queue_map,
            virt_tx_data_map,
            driver_virt_tx_ch.id_for_pd(self.virt_tx),
        )

        driver_rx_conn = None
        if self.virt_rx:
            driver_rx_queue_mr = MemoryRegion(
                self.sdf, "serial_driver_rx_queue", self.queue_size
            )
            driver_rx_data_mr = MemoryRegion(
                self.sdf, "serial_driver_rx_data", self.data_size
            )

            driver_rx_queue_map = self.driver.create_automap(
                driver_rx_queue_mr, Map.Permissions(r=True, w=True)
            )
            driver_rx_data_map = self.driver.create_automap(
                driver_rx_data_mr, Map.Permissions(r=True, w=True)
            )
            virt_rx_queue_map = self.virt_rx.create_automap(
                driver_rx_queue_mr, Map.Permissions(r=True, w=True)
            )
            virt_rx_data_map = self.virt_rx.create_automap(
                driver_rx_data_mr, Map.Permissions(r=True, w=True)
            )

            driver_virt_rx_ch = Channel(
                self.sdf,
                Channel.End(self.driver, can_notify=True, can_pp=False),
                Channel.End(self.virt_rx, can_notify=True, can_pp=False),
            )

            driver_rx_conn = self.serial_connection_resource_factory(
                driver_rx_queue_map,
                driver_rx_data_map,
                driver_virt_rx_ch.id_for_pd(self.driver),
            )
            self.virt_rx_driver_conn = self.serial_connection_resource_factory(
                virt_rx_queue_map,
                virt_rx_data_map,
                driver_virt_rx_ch.id_for_pd(self.virt_rx),
            )

        self.driver_config = self.serial_driver_config_factory(
            self.driver,
            SERIAL_PROTOCOL_MAGIC,
            self.baud_rate,
            1 if self.virt_rx else 0,
            driver_tx_conn,
            driver_rx_conn,
        )

    def connect_clients(self):
        assert self.virt_tx is not None
        assert self.driver is not None

        virt_tx_client_structs = []
        virt_rx_client_conns = []
        client_configs = []

        for c in self.clients:
            if c.priority >= self.virt_tx.priority:
                raise SubsystemBuildError(
                    f"Client {c} has a priority higher than virt_tx's "
                    f"({self.virt_tx.priority})!"
                )
            if self.virt_rx and c.priority >= self.virt_rx.priority:
                raise SubsystemBuildError(
                    f"Client {c} has a priority higher than virt_rx's "
                    f"({self.virt_rx.priority})!"
                )

            # TX connection: virt_tx -> client
            tx_queue_mr = MemoryRegion(
                self.sdf, f"serial_tx_queue_{c.name}", self.queue_size
            )
            tx_data_mr = MemoryRegion(
                self.sdf, f"serial_tx_data_{c.name}", self.data_size
            )

            virt_tx_tx_queue_map = self.virt_tx.create_automap(
                tx_queue_mr, Map.Permissions(r=True, w=True)
            )
            virt_tx_tx_data_map = self.virt_tx.create_automap(
                tx_data_mr, Map.Permissions(r=True, w=True)
            )
            c_tx_queue_map = c.create_automap(
                tx_queue_mr, Map.Permissions(r=True, w=True)
            )
            c_tx_data_map = c.create_automap(
                tx_data_mr, Map.Permissions(r=True, w=True)
            )

            tx_ch = Channel(
                self.sdf,
                Channel.End(self.virt_tx, can_notify=True, can_pp=False),
                Channel.End(c, can_notify=True, can_pp=False),
            )

            virt_tx_conn = self.serial_connection_resource_factory(
                virt_tx_tx_queue_map, virt_tx_tx_data_map, tx_ch.id_for_pd(self.virt_tx)
            )
            client_tx_conn = self.serial_connection_resource_factory(
                c_tx_queue_map, c_tx_data_map, tx_ch.id_for_pd(c)
            )

            virt_tx_client_structs.append(
                self.serial_virt_tx_client_config_factory(c.name, virt_tx_conn)
            )

            # RX connection (if enabled): virt_rx -> client
            client_rx_conn = None
            if self.virt_rx:
                rx_queue_mr = MemoryRegion(
                    self.sdf, f"serial_rx_queue_{c.name}", self.queue_size
                )
                rx_data_mr = MemoryRegion(
                    self.sdf, f"serial_rx_data_{c.name}", self.data_size
                )

                virt_rx_rx_queue_map = self.virt_rx.create_automap(
                    rx_queue_mr, Map.Permissions(r=True, w=True)
                )
                virt_rx_rx_data_map = self.virt_rx.create_automap(
                    rx_data_mr, Map.Permissions(r=True, w=True)
                )
                c_rx_queue_map = c.create_automap(
                    rx_queue_mr, Map.Permissions(r=True, w=True)
                )
                c_rx_data_map = c.create_automap(
                    rx_data_mr, Map.Permissions(r=True, w=True)
                )

                rx_ch = Channel(
                    self.sdf,
                    Channel.End(self.virt_rx, can_notify=True, can_pp=False),
                    Channel.End(c, can_notify=True, can_pp=False),
                )

                virt_rx_conn = self.serial_connection_resource_factory(
                    virt_rx_rx_queue_map,
                    virt_rx_rx_data_map,
                    rx_ch.id_for_pd(self.virt_rx),
                )
                client_rx_conn = self.serial_connection_resource_factory(
                    c_rx_queue_map, c_rx_data_map, rx_ch.id_for_pd(c)
                )
                virt_rx_client_conns.append(virt_rx_conn)

            client_configs.append(
                self.serial_client_config_factory(
                    c, SERIAL_PROTOCOL_MAGIC, client_tx_conn, client_rx_conn
                )
            )

        self.virt_tx_config = self.serial_virt_tx_config_factory(
            self.virt_tx,
            SERIAL_PROTOCOL_MAGIC,
            len(self.clients),
            self.virt_tx_driver_conn,
            virt_tx_client_structs,
            1 if self.enable_color else 0,
            1 if self.virt_rx else 0,
            self.begin_str,
        )

        if self.virt_rx:
            self.virt_rx_config = self.serial_virt_rx_config_factory(
                self.virt_rx,
                SERIAL_PROTOCOL_MAGIC,
                len(self.clients),
                self.virt_rx_driver_conn,
                virt_rx_client_conns,
            )

        self.client_configs = client_configs

    def x86_resources(self):
        self.add_x86_serial_port()

    def generate_config_structs(self):
        # We've already made our structs, just return them as a list for the serialiser
        driver_resources = [self.driver_dev_resources, self.driver_config]
        virt_resources = []
        if self.virt_tx_config:
            virt_resources.append(self.virt_tx_config)
        if self.virt_rx_config:
            virt_resources.append(self.virt_rx_config)
        return driver_resources + virt_resources + self.client_configs

    # ### connection config struct factory functions ###

    def serial_connection_resource_factory(
        self, queue_map: Map, data_map: Map, ch_id: int
    ) -> ConfigStruct:
        fields = {
            "queue": RegionResourceFactory(queue_map),
            "data": RegionResourceFactory(data_map),
            "id": ch_id,
        }
        return ConfigStruct("serial_connection_resource_t", fields=fields)

    def serial_driver_config_factory(
        self,
        driver_pd: ProtectionDomain,
        magic: str,
        baud_rate: int,
        rx_enabled: int,
        tx_connection: ConfigStruct,
        rx_connection: Optional[ConfigStruct] = None,
    ) -> ConfigStruct:
        fields = {
            "magic": magic,
            "default_baud": baud_rate,
            "rx_enabled": rx_enabled,
            "tx": tx_connection,
            "rx": rx_connection if rx_connection else 0,
        }
        return ConfigStruct(
            "serial_driver_config_t",
            target_file=driver_pd.prog_image,
            section_name="serial_driver_config",
            fields=fields,
        )

    def serial_virt_rx_config_factory(
        self,
        virt_rx_pd: ProtectionDomain,
        magic: str,
        num_clients: int,
        driver_connection: ConfigStruct,
        client_connections: List[ConfigStruct],
    ) -> ConfigStruct:
        fields = {
            "magic": magic,
            "num_clients": num_clients,
            "driver": driver_connection,
            "clients": client_connections,
            "switch_char": chr(28),
            "terminate_num_char": "\r",
        }
        return ConfigStruct(
            "serial_virt_rx_config_t",
            target_file=virt_rx_pd.prog_image,
            section_name="serial_virt_rx_config",
            fields=fields,
        )

    def serial_virt_tx_client_config_factory(
        self, name: str, conn: ConfigStruct
    ) -> ConfigStruct:
        fields = {
            "conn": conn,
            "name": name,
        }
        return ConfigStruct("serial_virt_tx_client_t", fields=fields)

    def serial_virt_tx_config_factory(
        self,
        virt_tx_pd: ProtectionDomain,
        magic: str,
        num_clients: int,
        driver_connection: ConfigStruct,
        client_connections: List[ConfigStruct],
        enable_colour: int,
        enable_rx: int,
        begin_str: str,
    ) -> ConfigStruct:
        fields = {
            "magic": magic,
            "driver": driver_connection,
            "clients": client_connections,
            "num_clients": num_clients,
            "begin_str": begin_str,
            "enable_colour": enable_colour,
            "enable_rx": enable_rx,
        }
        return ConfigStruct(
            "serial_virt_tx_config_t",
            target_file=virt_tx_pd.prog_image,
            section_name="serial_virt_tx_config",
            fields=fields,
        )

    def serial_client_config_factory(
        self,
        client_pd: ProtectionDomain,
        magic,
        tx_connection: ConfigStruct,
        rx_connection: Optional[ConfigStruct] = None,
    ) -> ConfigStruct:
        fields = {
            "magic": magic,
            "tx": tx_connection,
            "rx": rx_connection if rx_connection else 0,
        }
        return ConfigStruct(
            "serial_client_config_t",
            target_file=client_pd.prog_image,
            section_name="serial_client_config",
            fields=fields,
        )

    # x86 Util
    def add_x86_serial_port(self):
        # The serial device does not located on PCIe and the interrupts are
        # conventionally configured by BIOS. The IRQ number can be read from
        # Linux or APCI tables.
        self.driver.add_ioport(IOPort(0x3F8, 8, 0))
        self.driver.add_irq(IrqIoapic(0, 4, 0, id=1))


# Driver configs
serial_driver_configs: Dict[str, List[sDDFDriverConfig]] = defaultdict(list)


def add_driver_config(driver_name: str, config: sDDFDriverConfig):
    sDDFDriverManifest().add_driver_config(sDDFSerial, driver_name, config)


add_driver_config(
    "meson",
    sDDFDriverConfig(
        ["amlogic,meson-gx-uart", "amlogic,meson-ao-uart"],
        [DTSRegion("regs", "rw", 4096, 0)],
        [DTSIRQ(0)],
    ),
)

add_driver_config(
    "pl011",
    sDDFDriverConfig(
        compatible="arm,pl011",
        regions=[DTSRegion("regs", "rw", 4096, 0)],
        irqs=[DTSIRQ(0)],
    ),
)

add_driver_config(
    "imx",
    sDDFDriverConfig(
        compatible=["fsl,imx8mq-uart", "fsl,imx8mm-uart", "fsl,imx8mp-uart"],
        regions=[DTSRegion("regs", "rw", 4096, 0)],
        irqs=[DTSIRQ(0)],
    ),
)

# ns16550a
add_driver_config(
    "ns16550a",
    sDDFDriverConfig(
        compatible=[
            "starfive,jh7110-uart",
            "ns16550a",
            "brcm,bcm2835-aux-uart",
            "snps,dw-apb-uart",
        ],
        regions=[DTSRegion("regs", "rw", 4096, 0)],
        irqs=[DTSIRQ(0)],
    ),
)

# virtio
add_driver_config(
    "virtio",
    sDDFDriverConfig(
        compatible="virtio,mmio",
        regions=[
            DTSRegion("regs", "rw", 4096, 0),
            DTSRegion("hw_ring_buffer", size=65536),
            DTSRegion("virtio_rx_buf", size=4096),
            DTSRegion("virtio_tx_buf", size=4096),
        ],
        irqs=[DTSIRQ(0)],
    ),
)

# xlnx
add_driver_config(
    "xlnx",
    sDDFDriverConfig(
        compatible="xlnx,zynqmp-uart",
        regions=[DTSRegion("regs", dt_idx=0)],
        irqs=[DTSIRQ(0)],
    ),
)
