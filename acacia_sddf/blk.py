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
import sys, os
from collections import defaultdict
from typing import List, Dict, Type, Union, Optional
from dataclasses import dataclass
from acacia.x86 import IOPort
from acacia.irq import IrqIoapic
from .driver_manifest import sDDFDriverManifest, sDDFDriverConfig, DTSIRQ, DTSRegion
from .sddf import (
    sDDFDriverClass,
    DeviceResourcesFactory,
    RegionResourceFactory,
    DeviceRegionResourceFactory,
)

BLK_PROTOCOL_MAGIC = "sDDF" + chr(0x2)
BLK_STORAGE_INFO_SZ = 0x1000


@dataclass(frozen=True)
class BlkClientOptions:
    partition_number: int
    queue_capacity: int = 128
    data_size: int = 2 * 1024 * 1024  # 2 mibibyte


class sDDFBlk(sDDFDriverClass):

    def __init__(
        self,
        sdf: System,
        dev_compatible: str,
        dev_dt_path: str,
        driver_prio: int,
        virt_prio: int,
        cpu: Optional[int] = None,
        # We leave this as configurable just in case...
        driver_data_size: int = 0x1000,
        virt_elf: str = "blk_virt.elf",
        driver_elf: str = "blk_driver.elf",
    ):
        assert driver_prio > virt_prio > 0

        self.cpu = cpu
        self.driver_data_size = driver_data_size
        self.virt = None
        self.virt_elf = virt_elf
        driver = ProtectionDomain(
            sdf,
            "blk_driver",
            driver_elf,
            scheduling=SchedulingProperties(driver_prio),
            cpu=self.cpu,
        )
        super().__init__(
            sdf, driver, "blk", dev_compatible, dev_dt_path, magic="sDDF" + chr(0x1)
        )

        # Client config dict. Maps client PD object -> options.
        self.client_blk_configs: Dict[ProtectionDomain, BlkClientOptions] = {}

        # Stubs of config structs that we need to collect in construct_infrastructure and connect_clients
        self.virt_config = None
        self.driver_config = None
        self.virt_driver_conn = None
        self.client_config_protos = []
        self.construct_infrastructure(virt_prio)

    def construct_infrastructure(self, virt_prio: int):
        self.virt = ProtectionDomain(
            self.sdf,
            "blk_virt",
            self.virt_elf,
            scheduling=SchedulingProperties(virt_prio),
            cpu=self.cpu,
        )

        strg_info_mr = MemoryRegion(
            self.sdf, "blk_driver_storage_info", BLK_STORAGE_INFO_SZ
        )
        self.driver_info_map = self.driver.create_automap(
            strg_info_mr, Map.Permissions(r=True, w=True)
        )
        self.virt_info_map = self.virt.create_automap(
            strg_info_mr, Map.Permissions(r=True, w=False)
        )

        # used in blk/components/partitioning.c
        self.driver_data_mr = MemoryRegion(
            self.sdf, "blk_driver_data", self.driver_data_size, physical=True
        )

        # We can't create the request or response queues now since their size depends
        # on the number of clients. We do it after connecting clients instead.
        self.driver_virt_ch = Channel(
            self.sdf,
            Channel.End(self.driver, can_notify=True, can_pp=False),
            Channel.End(self.virt, can_notify=True, can_pp=False),
        )

    def create_driver_virt_connection(self):
        driver_q_capacity = sum(
            [
                self.client_blk_configs[cc].queue_capacity
                for cc in self.client_blk_configs
            ]
        )
        assert driver_q_capacity > 0
        driver_q_mr_sz = driver_q_capacity * 128

        # Make maps from data region created in create_infrastructure
        virt_data_map = self.virt.create_automap(
            self.driver_data_mr, Map.Permissions(r=True, w=True)
        )

        # queue regions
        driver_req_mr = MemoryRegion(self.sdf, "blk_driver_request", driver_q_mr_sz)
        driver_resp_mr = MemoryRegion(self.sdf, "blk_driver_response", driver_q_mr_sz)

        driver_req_map = self.driver.create_automap(
            driver_req_mr, Map.Permissions(r=True, w=True)
        )
        driver_resp_map = self.driver.create_automap(
            driver_resp_mr, Map.Permissions(r=True, w=True)
        )
        virt_req_map = self.virt.create_automap(
            driver_req_mr, Map.Permissions(r=True, w=True)
        )
        virt_resp_map = self.virt.create_automap(
            driver_resp_mr, Map.Permissions(r=True, w=True)
        )

        # Create driver config
        driver_virt_conn = self.blk_connection_resource_factory(
            self.driver_info_map,
            driver_req_map,
            driver_resp_map,
            self.driver_virt_ch.id_for_pd(self.driver),
            driver_q_capacity,
        )
        self.driver_config = self.blk_driver_config_factory(
            self.driver, BLK_PROTOCOL_MAGIC, driver_virt_conn
        )

        # Create virt's driver config
        virt_driver_conn = self.blk_connection_resource_factory(
            self.virt_info_map,
            virt_req_map,
            virt_resp_map,
            self.driver_virt_ch.id_for_pd(self.virt),
            driver_q_capacity,
        )

        # Store a tuple of args to the factory, since the data MR isn't assigned a paddr until
        # assembly time.
        self.virt_driver_config_proto = (virt_driver_conn, virt_data_map)

    def add_client(
        self,
        client: ProtectionDomain,
        partition_number: int,
        queue_capacity: Optional[int] = BlkClientOptions.queue_capacity,
        data_size: Optional[int] = BlkClientOptions.data_size,
    ):
        self.client_blk_configs[client] = BlkClientOptions(
            partition_number, queue_capacity, data_size
        )
        super().add_client(client)

    def connect_clients(self):
        assert self.virt is not None
        assert self.driver is not None

        virt_client_struct_protos = []
        virt_rx_client_conns = []
        client_config_protos = []

        for c in self.clients:
            if c.priority >= self.virt.priority:
                raise SubsystemBuildError(
                    f"Client {c} has a priority higher than virt's "
                    f"({self.virt.priority})!"
                )
            cfg = self.client_blk_configs[c]
            assert cfg is not None

            strg_info_mr = MemoryRegion(
                self.sdf, f"blk_client_{c.name}_storage_info", BLK_STORAGE_INFO_SZ
            )
            virt_strg_map = self.virt.create_automap(
                strg_info_mr, Map.Permissions(r=True, w=True)
            )
            client_strg_map = c.create_automap(
                strg_info_mr, Map.Permissions(r=True, w=False)
            )

            queue_mr_sz = cfg.queue_capacity * 128
            req_mr = MemoryRegion(self.sdf, f"blk_client_{c.name}_request", queue_mr_sz)
            resp_mr = MemoryRegion(
                self.sdf, f"blk_client_{c.name}_response", queue_mr_sz
            )
            data_mr = MemoryRegion(
                self.sdf, f"blk_client_{c.name}_data", cfg.data_size, physical=True
            )

            client_req_map = c.create_automap(req_mr, Map.Permissions(r=True, w=True))
            client_resp_map = c.create_automap(resp_mr, Map.Permissions(r=True, w=True))
            client_data_map = c.create_automap(data_mr, Map.Permissions(r=True, w=True))
            virt_req_map = self.virt.create_automap(
                req_mr, Map.Permissions(r=True, w=True)
            )
            virt_resp_map = self.virt.create_automap(
                resp_mr, Map.Permissions(r=True, w=True)
            )
            virt_data_map = self.virt.create_automap(
                data_mr, Map.Permissions(r=True, w=True)
            )

            ch = Channel(
                self.sdf,
                Channel.End(self.virt, can_notify=True, can_pp=False),
                Channel.End(c, can_notify=True, can_pp=False),
            )

            virt_conn = self.blk_connection_resource_factory(
                virt_strg_map,
                virt_req_map,
                virt_resp_map,
                ch.id_for_pd(self.virt),
                cfg.queue_capacity,
            )
            client_conn = self.blk_connection_resource_factory(
                client_strg_map,
                client_req_map,
                client_resp_map,
                ch.id_for_pd(c),
                cfg.queue_capacity,
            )

            # Store the args to the config struct factories now, but don't
            # make the config structs until `generate_config_structs` is called.
            virt_client_struct_protos.append(
                (virt_data_map, virt_conn, cfg.partition_number)
            )

            client_config_protos.append(
                (c, BLK_PROTOCOL_MAGIC, client_conn, client_data_map)
            )

        self.client_config_protos = client_config_protos
        self.virt_client_struct_protos = virt_client_struct_protos

        # Create driver-virt queues now that we know how they should be sized.
        self.create_driver_virt_connection()

    def x86_resources(self):
        # Nothing needed for now?
        ...

    def generate_config_structs(self):
        # Assemble configs that depended on an unassigned paddr, now that
        # Acacia has assigned all paddrs.
        client_configs = [
            self.blk_client_config_factory(*c) for c in self.client_config_protos
        ]
        virt_client_structs = [
            self.blk_virt_client_config_factory(*vc)
            for vc in self.virt_client_struct_protos
        ]
        self.virt_config = self.blk_virt_config_factory(
            self.virt,
            BLK_PROTOCOL_MAGIC,
            self.blk_virt_driver_config_factory(*self.virt_driver_config_proto),
            virt_client_structs,
        )
        return (
            super().generate_config_structs()
            + [self.driver_config, self.virt_config]
            + client_configs
        )

    # ### connection config struct factory functions ###

    def blk_connection_resource_factory(
        self,
        strg_info_map: Map,
        req_map: Map,
        resp_map: Map,
        ch_id: int,
        num_buffers: int,
    ) -> ConfigStruct:
        fields = {
            "storage_info": RegionResourceFactory(strg_info_map),
            "req_queue": RegionResourceFactory(req_map),
            "resp_queue": RegionResourceFactory(resp_map),
            "num_buffers": num_buffers,
            "id": ch_id,
        }
        return ConfigStruct("blk_connection_resource_t", fields=fields)

    def blk_driver_config_factory(
        self,
        driver_pd: ProtectionDomain,
        magic: str,
        virt_connection: ConfigStruct,
    ) -> ConfigStruct:
        fields = {"magic": magic, "virt": virt_connection}
        return ConfigStruct(
            "blk_driver_config_t",
            target_file=driver_pd.prog_image,
            section_name="blk_driver_config",
            fields=fields,
        )

    def blk_virt_client_config_factory(
        self, data_map: Map, conn: ConfigStruct, partition_no: int
    ) -> ConfigStruct:
        """
        Config telling the virt about a client.
        """
        fields = {
            "conn": conn,
            "data": DeviceRegionResourceFactory(
                RegionResourceFactory(data_map), data_map.mr.paddr
            ),
            "partition": partition_no,
        }
        return ConfigStruct("blk_virt_client_t", fields=fields)

    def blk_virt_driver_config_factory(
        self, driver_conn: ConfigStruct, data_map: Map
    ) -> ConfigStruct:
        """
        Config telling virt about the driver.
        """
        fields = {
            "conn": driver_conn,
            "data": DeviceRegionResourceFactory(
                RegionResourceFactory(data_map), data_map.mr.paddr
            ),
        }
        return ConfigStruct("blk_virt_client_t", fields=fields)

    def blk_virt_config_factory(
        self,
        virt_pd: ProtectionDomain,
        magic: str,
        virt_driver_config: ConfigStruct,
        virt_client_config_protos: List[ConfigStruct],
    ) -> ConfigStruct:
        assert len(virt_client_config_protos) == len(self.clients)
        fields = {
            "magic": magic,
            "num_clients": len(virt_client_config_protos),
            "driver": virt_driver_config,
            "clients": virt_client_config_protos,
        }
        return ConfigStruct(
            "blk_virt_config_t",
            target_file=virt_pd.prog_image,
            section_name="blk_virt_config",
            fields=fields,
        )

    def blk_client_config_factory(
        self,
        client_pd: ProtectionDomain,
        magic,
        virt_connection: ConfigStruct,
        data_map: Map,
    ) -> ConfigStruct:
        fields = {
            "magic": magic,
            "virt": virt_connection,
            "data": RegionResourceFactory(data_map),
        }
        return ConfigStruct(
            "blk_client_config_t",
            target_file=client_pd.prog_image,
            section_name="blk_client_config",
            fields=fields,
        )


# Driver configs
def add_driver_config(driver_name: str, config: sDDFDriverConfig):
    sDDFDriverManifest().add_driver_config(sDDFBlk, driver_name, config)


add_driver_config(
    "imx",
    sDDFDriverConfig(
        compatible=["fsl,imx8mq-usdhc", "fsl,imx7d-usdhc"],
        regions=[DTSRegion("regs", "rw", 65536, 0)],
        irqs=[DTSIRQ(0)],
    ),
)

# virtio
add_driver_config(
    "virtio",
    sDDFDriverConfig(
        compatible=["virtio,mmio"],
        regions=[
            DTSRegion("regs", "rw", 4096, 0),
            DTSRegion("virtio_headers", size=65536),
            DTSRegion("virtio_metadata", size=2097152),
        ],
        irqs=[DTSIRQ(0)],
    ),
)
