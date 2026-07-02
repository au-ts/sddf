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
)
import sys, os
from collections import defaultdict
from dataclasses import dataclass
from typing import List, Dict, Type, Union, Optional
from .driver_manifest import sDDFDriverManifest, sDDFDriverConfig, DTSIRQ, DTSRegion
from .sddf import sDDFDriverClass, DeviceResourcesFactory, RegionResourceFactory

I2C_DATA_SZ = 0x1000
I2C_NUM_BUFS = 128  # TODO: add support for dynamically sized queues
I2C_PROTOCOL_MAGIC = "sDDF" + chr(0x4)


@dataclass
class I2CAddress:
    addr: int

    def __post_init__(self):
        if self.addr & (1 << 31):
            # This bit is set in DTS I2C addresses to mark 10 bit addresses.
            # If found, we strip it out and store a bool.
            self.is_ten_bit = True
            self.addr &= ~(1 << 31)
        else:
            self.is_ten_bit = False


class sDDFI2C(sDDFDriverClass):
    def __init__(
        self,
        sdf: System,
        dev_compatible: str,
        dev_dt_path: str,
        driver_prio: int,
        virt_prio: int,
        cpu: Optional[int] = None,
        virt_elf: str = "i2c_virt.elf",
        driver_elf: str = "i2c_driver.elf",
    ):
        super().__init__(
            sdf, "i2c", dev_compatible, dev_dt_path, magic="sDDF" + chr(0x1)
        )
        self.sdf = sdf
        self.cpu = cpu

        # Internal bookkeeping
        self.driver = None
        self.virt = None

        # ELF names. This is required because acacia is tragically detached
        # from the build system itself and cannot guarantee the names of sDDF
        # compiled objects itself. This will not be required once we start using
        # the sDDF with an SDK model, but that is for the future.
        self.virt_elf = virt_elf
        self.driver = ProtectionDomain(
            self.sdf,
            "i2c_driver",
            driver_elf,
            scheduling=SchedulingProperties(driver_prio),
            cpu=self.cpu,
        )

        # We must make the driver BEFORE we get here
        self.driver_dev_resources = self.create_dtb_resources(self.driver)

        # Stubs of config structs that we need to collect in construct_infrastructure and connect_clients
        self.virt_config = None
        self.driver_config = None
        self.virt_driver_config = None
        self.client_configs = []
        self.channels = []

        # Special cases for boards. These should be removed once we add infrastructure to support this better.
        # meson (odroidc4/5)
        if "amlogic,meson" in dev_compatible:
            # Odroid-C4 I2C requires clocks/GPIO setup, for now we give the I2C driver
            # direct access.
            clk_mr = MemoryRegion(
                self.sdf, "clk", 0x1000, paddr=0xFF63C000, cached=False
            )
            gpio_mr = MemoryRegion(
                self.sdf, "gpio", 0x1000, paddr=0xFF634000, cached=False
            )
            self.driver.add_map(Map(clk_mr, 0x30_000_000, "rw"))
            self.driver.add_map(Map(gpio_mr, 0x30_100_000, "rw"))

        # We create queues etc. AFTER setting up the device resources to ensure that IRQ channels
        # have a lower value than any other channels. This is necessary because Microkit will
        # deliver notifications in ascending channel_id order, which can end up mattering in certain
        # cases.
        self.construct_infrastructure(virt_prio)

    def construct_infrastructure(self, virt_prio):
        self.virt = ProtectionDomain(
            self.sdf,
            "i2c_virt",
            self.virt_elf,
            scheduling=SchedulingProperties(virt_prio),
            cpu=self.cpu,
        )

        # Make queues
        driver_req_q_mr = MemoryRegion(self.sdf, "i2c_driver_request", 0x1000)
        driver_resp_q_mr = MemoryRegion(self.sdf, "i2c_driver_response", 0x1000)
        driver_req_map = self.driver.create_automap(
            driver_req_q_mr, Map.Permissions(r=True, w=True)
        )
        driver_resp_map = self.driver.create_automap(
            driver_resp_q_mr, Map.Permissions(r=True, w=True)
        )
        virt_req_map = self.virt.create_automap(
            driver_req_q_mr, Map.Permissions(r=True, w=True)
        )
        virt_resp_map = self.virt.create_automap(
            driver_resp_q_mr, Map.Permissions(r=True, w=True)
        )

        # Create channels
        driver_virt_ch = Channel(
            self.sdf,
            Channel.End(self.driver, can_notify=True, can_pp=False),
            Channel.End(self.virt, can_notify=True, can_pp=False),
            self.sdf,
        )
        self.channels.append(driver_virt_ch)

        # Create config structs
        self.virt_driver_config = self.i2c_connection_resource_factory(
            virt_req_map,
            virt_resp_map,
            I2C_NUM_BUFS,
            driver_virt_ch.id_for_pd(self.virt),
        )
        driver_virt_connection = self.i2c_connection_resource_factory(
            driver_req_map,
            driver_resp_map,
            I2C_NUM_BUFS,
            driver_virt_ch.id_for_pd(self.driver),
        )
        self.driver_config = self.i2c_driver_config_factory(
            self.driver, I2C_PROTOCOL_MAGIC, driver_virt_connection
        )

    def connect_clients(self):
        assert self.virt is not None
        assert self.driver is not None

        # Clients are connected with:
        # a. request queue
        # b. response queue
        # c. data region shared with driver
        # c. channel for notifications and PPCs
        virt_client_configs = []
        for c in self.clients:
            if c.priority >= self.virt.priority:
                raise SubsystemBuildError(
                    f"Client {c} has a priority higher "
                    f"than virt's ({self.driver.priority})!"
                )
            # Make channel
            ch = Channel(
                self.sdf,
                Channel.End(c, can_notify=True, can_pp=True),
                Channel.End(self.virt, can_notify=True, can_pp=False),
                self.sdf,
            )
            self.channels.append(ch)

            # Add request and response queue
            c_req_q_mr = MemoryRegion(f"i2c_client_request_{c.name}", 0x1000, self.sdf)
            c_resp_q_mr = MemoryRegion(
                f"i2c_client_response_{c.name}", 0x1000, self.sdf
            )
            c_data_mr = MemoryRegion(f"i2c_client_data_{c.name}", I2C_DATA_SZ, self.sdf)

            # Create maps for clients
            c_req_map = c.create_automap(c_req_q_mr, Map.Permissions(r=True, w=True))
            c_resp_map = c.create_automap(c_resp_q_mr, Map.Permissions(r=True, w=True))
            c_data_map = c.create_automap(c_data_mr, Map.Permissions(r=True, w=True))

            # Maps for virt / driver
            req_map = self.virt.create_automap(
                c_req_q_mr, Map.Permissions(r=True, w=True)
            )
            resp_map = self.virt.create_automap(
                c_resp_q_mr, Map.Permissions(r=True, w=True)
            )
            data_map = self.driver.create_automap(
                c_data_mr, Map.Permissions(r=True, w=True)
            )

            # Prep config structs
            virt_connection = self.i2c_connection_resource_factory(
                req_map, resp_map, I2C_NUM_BUFS, ch.id_for_pd(self.virt)
            )
            client_connection = self.i2c_connection_resource_factory(
                c_req_map, c_resp_map, I2C_NUM_BUFS, ch.id_for_pd(c)
            )
            client_data = RegionResourceFactory(c_data_map)

            self.client_configs.append(
                self.i2c_client_config_factory(c, client_connection, client_data)
            )
            virt_client_configs.append(
                self.i2c_virt_client_config_factory(
                    virt_connection, I2C_DATA_SZ, data_map.vaddr, c_data_map.vaddr
                )
            )
        # Clients added. Finally, create virt config
        self.virt_config = self.i2c_virt_config_factory(
            self.virt,
            I2C_PROTOCOL_MAGIC,
            len(self.clients),
            self.virt_driver_config,
            virt_client_configs,
        )

    def generate_config_structs(self):
        # We've already made our structs, just return them as a list for the serialiser
        driver_resources = [self.driver_dev_resources, self.driver_config]
        virt_resources = [self.virt_config]
        return driver_resources + virt_resources + self.client_configs

    # ### dtb utility functions for drivers that depend on i2c ###
    def get_i2c_addresses_from_dtb(self, device_node: DTBNode) -> List[I2CAddress]:
        """
        Try and get the i2c addresses of a device on the bus controlled by this driver.

        If the path given is not for this I2C bus or the device is not present, a
        ValueError will be raised.
        Args:
            device_node: DTBNode - peripheral node
        Returns:
            List[I2CAddress]
        """
        # first: check that this path belongs to us
        if self.dtb_node.path not in device_node.path:
            raise ValueError(
                f"{device_node} doesn't belong to this I2C bus ({self.dtb_node.path})!"
            )

        # reg property contains addresses.
        reg = [x[0] for x in self.dtb.get_node_regs(device_node)]
        return [I2CAddress(int(x)) for x in reg]

    # ### connection config struct factory functions ###
    def i2c_connection_resource_factory(
        self, req_q: Map, resp_q: Map, num_bufs: int, id: int
    ) -> ConfigStruct:
        fields = {
            "req_queue": RegionResourceFactory(req_q),
            "resp_queue": RegionResourceFactory(resp_q),
            "num_buffers": num_bufs,
            "id": id,
        }
        return ConfigStruct("i2c_connection_resource_t", fields=fields)

    def i2c_client_config_factory(
        self,
        client_pd: ProtectionDomain,
        virt_connection: ConfigStruct,
        data_region: ConfigStruct,
    ) -> ConfigStruct:
        """
        Create i2c_client_config for client_pd with serial id n
        """
        # invariant: this PD only is a client to i2c one time.
        end = next(x.end_a for x in self.channels if x.end_a.pd is client_pd)
        ch_id = end.ch_id
        fields = {
            "magic": I2C_PROTOCOL_MAGIC,
            "virt": virt_connection,
            "data": data_region,
        }
        return ConfigStruct(
            "i2c_client_config_t",
            target_file=client_pd.prog_image,
            section_name="i2c_client_config",
            fields=fields,
        )

    def i2c_virt_client_config_factory(
        self,
        client_connection: ConfigStruct,
        data_size: int,
        driver_d_vaddr: int,
        client_d_vaddr: int,
    ) -> ConfigStruct:
        """
        Create a i2c_virt_client_config for some client.
        """
        fields = {
            "conn": client_connection,
            "data_size": data_size,
            "driver_data_vaddr": driver_d_vaddr,
            "client_data_vaddr": client_d_vaddr,
        }
        return ConfigStruct("i2c_virt_client_config_t", fields=fields)

    def i2c_virt_config_factory(
        self,
        virt_pd: ProtectionDomain,
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
        }
        return ConfigStruct(
            "i2c_virt_config_t",
            target_file=virt_pd.prog_image,
            section_name="i2c_virt_config",
            fields=fields,
        )

    def i2c_driver_config_factory(
        self, driver_pd: ProtectionDomain, magic: str, virt_connection: ConfigStruct
    ) -> ConfigStruct:
        fields = {
            "magic": magic,
            "virt": virt_connection,
        }
        return ConfigStruct(
            "i2c_driver_config_t",
            target_file=driver_pd.prog_image,
            section_name="i2c_driver_config",
            fields=fields,
        )


# Driver configs
i2c_driver_configs: Dict[str, List[sDDFDriverConfig]] = defaultdict(list)


def add_driver_config(driver_name: str, config: sDDFDriverConfig):
    sDDFDriverManifest().add_driver_config(sDDFI2C, driver_name, config)


# meson
add_driver_config(
    "meson",
    sDDFDriverConfig(
        compatible="amlogic,meson-axg-i2c",
        regions=[DTSRegion("regs", "rw", 4096, 0)],
        irqs=[DTSIRQ(0), DTSIRQ(1)],
    ),
)

# opentitan
add_driver_config(
    "opentitan",
    sDDFDriverConfig(
        compatible="eth,i2c",
        regions=[DTSRegion("regs", "rw", 4096, 0)],
        irqs=[DTSIRQ(4), DTSIRQ(0), DTSIRQ(1), DTSIRQ(7), DTSIRQ(9)],
    ),
)

# imx (8mq only for now? untested on others)
add_driver_config(
    "imx",
    sDDFDriverConfig(
        compatible=["fsl,imx8mq-i2c", "fsl,imx21-i2c"],
        regions=[DTSRegion("regs", "rw", 4096, 0)],
        irqs=[DTSIRQ(0)],
    ),
)
