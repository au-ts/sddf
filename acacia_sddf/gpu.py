# Copyright 2026, UNSW
# SPDX-License-Identifier: BSD-2-Clause

from dataclasses import dataclass
from typing import Dict, List, Optional

from acacia import (
    Channel,
    ConfigStruct,
    Map,
    MemoryRegion,
    ProtectionDomain,
    SchedulingProperties,
    SubsystemBuildError,
    System,
    build_hook,
)

from .driver_manifest import register_sddf_subsystem
from .sddf import (
    DeviceRegionResourceFactory,
    RegionResourceFactory,
    sDDFDriverClass,
)

# Must match include/sddf/gpu/config.h
GPU_PROTOCOL_MAGIC = "sDDF" + chr(0x7)
GPU_MAX_CLIENTS = 64
GPU_MAX_QUEUE_CAPACITY = 1024

# Queue layout (include/sddf/gpu/queue.h): a {head, tail} header followed by entries.
# sizeof(gpu_req_t) is 56 bytes on 64-bit targets, we round up to leave headroom.
GPU_QUEUE_HEADER_SZ = 8
GPU_REQ_ENTRY_SZ = 64
GPU_RESP_ENTRY_SZ = 8
GPU_EVENTS_REGION_SZ = 0x1000


@dataclass(frozen=True)
class GpuClientOptions:
    queue_capacity: int = 128
    data_size: int = 2 * 1024 * 1024  # 2 mebibytes


class sDDFGpu(sDDFDriverClass):
    """
    sDDF GPU device class: a driver, a virtualiser and any number of clients.

    Each client gets request/response queues, an events region (used to signal
    display info changes) and a physically contiguous data region. Clients back
    their resources with memory from their data region; the virtualiser
    translates offsets into that region into I/O addresses for the device.
    """

    def __init__(
        self,
        sdf: System,
        dev_compatible: str,
        dev_dt_path: str,
        driver_prio: int,
        virt_prio: int,
        cpu: Optional[int] = None,
        virt_elf: str = "gpu_virt.elf",
        driver_elf: str = "gpu_driver.elf",
    ):
        assert driver_prio > virt_prio > 0

        self.cpu = cpu
        self.virt = None
        self.virt_elf = virt_elf
        driver = ProtectionDomain(
            sdf,
            "gpu_driver",
            driver_elf,
            scheduling=SchedulingProperties(driver_prio),
            stack_size=0x10000,
            cpu=self.cpu,
        )
        super().__init__(
            sdf, driver, "gpu", dev_compatible, dev_dt_path, magic="sDDF" + chr(0x1)
        )

        self.client_gpu_configs: Dict[ProtectionDomain, GpuClientOptions] = {}

        self.driver_config = None
        self.virt_driver_config_proto = None
        self.virt_client_config_protos = []
        self.client_config_protos = []
        self.construct_infrastructure(virt_prio)

    def construct_infrastructure(self, virt_prio: int):
        self.virt = ProtectionDomain(
            self.sdf,
            "gpu_virt",
            self.virt_elf,
            scheduling=SchedulingProperties(virt_prio),
            stack_size=0x10000,
            cpu=self.cpu,
        )

        # The driver writes GET_DISPLAY_INFO responses here for the virt to read.
        self.driver_data_mr = MemoryRegion(
            self.sdf, "gpu_driver_data", 0x1000, physical=True
        )

        self.driver_virt_ch = Channel(
            self.sdf,
            Channel.End(self.virt, can_notify=True, can_pp=False),
            Channel.End(self.driver, can_notify=True, can_pp=False),
        )

    def add_client(
        self,
        client: ProtectionDomain,
        queue_capacity: int = GpuClientOptions.queue_capacity,
        data_size: int = GpuClientOptions.data_size,
    ):
        if client in self.client_gpu_configs:
            raise SubsystemBuildError(f"Duplicate gpu client {client.name}!")
        if client.name in (self.driver.name, self.virt.name):
            raise SubsystemBuildError(
                f"Invalid gpu client, same name as driver or virt '{client.name}'"
            )
        if len(self.client_gpu_configs) >= GPU_MAX_CLIENTS:
            raise SubsystemBuildError(
                f"Gpu supports at most {GPU_MAX_CLIENTS} clients!"
            )
        if not 0 < queue_capacity <= GPU_MAX_QUEUE_CAPACITY:
            raise SubsystemBuildError(
                f"Client {client.name} queue_capacity={queue_capacity} must be in "
                f"(0, {GPU_MAX_QUEUE_CAPACITY}]!"
            )
        if not self.sdf.arch.addr_is_page_aligned(data_size):
            raise SubsystemBuildError(
                f"Client data size {data_size} is not page aligned!"
            )
        self.client_gpu_configs[client] = GpuClientOptions(queue_capacity, data_size)
        super().add_client(client)

    def _queue_mrs(self, prefix: str, capacity: int):
        req_sz = self.sdf.arch.roundup_to_page(
            GPU_QUEUE_HEADER_SZ + capacity * GPU_REQ_ENTRY_SZ
        )
        resp_sz = self.sdf.arch.roundup_to_page(
            GPU_QUEUE_HEADER_SZ + capacity * GPU_RESP_ENTRY_SZ
        )
        events = MemoryRegion(self.sdf, f"{prefix}_events", GPU_EVENTS_REGION_SZ)
        req = MemoryRegion(self.sdf, f"{prefix}_request", req_sz)
        resp = MemoryRegion(self.sdf, f"{prefix}_response", resp_sz)
        return events, req, resp

    @build_hook  # Runs 1st / 2 (before client connection)
    def create_driver_virt_connection(self):
        if len(self.client_gpu_configs) == 0:
            raise SubsystemBuildError("Gpu subsystem has no clients!")

        # The virt bounds in-flight driver requests by this capacity, so it
        # just needs to be large enough to not throttle clients unnecessarily.
        driver_q_capacity = min(
            sum(c.queue_capacity for c in self.client_gpu_configs.values()) + 1,
            GPU_MAX_QUEUE_CAPACITY,
        )

        events_mr, req_mr, resp_mr = self._queue_mrs("gpu_driver", driver_q_capacity)
        rw = Map.Permissions(r=True, w=True)

        driver_maps = [self.driver.create_automap(mr, rw) for mr in (events_mr, req_mr, resp_mr)]
        virt_maps = [self.virt.create_automap(mr, rw) for mr in (events_mr, req_mr, resp_mr)]
        driver_data_map = self.driver.create_automap(self.driver_data_mr, rw)
        virt_data_map = self.virt.create_automap(self.driver_data_mr, rw)

        driver_conn = self.gpu_connection_resource_factory(
            *driver_maps, self.driver_virt_ch.id_for_pd(self.driver), driver_q_capacity
        )
        self.driver_config = self.gpu_driver_config_factory(
            self.driver, driver_conn, driver_data_map
        )

        virt_conn = self.gpu_connection_resource_factory(
            *virt_maps, self.driver_virt_ch.id_for_pd(self.virt), driver_q_capacity
        )
        # The data MR is only assigned a paddr at assembly time.
        self.virt_driver_config_proto = (virt_conn, virt_data_map)

    @build_hook  # Runs 2nd / 2. Must come after the driver-virt connection.
    def connect_clients(self):
        assert self.virt is not None
        rw = Map.Permissions(r=True, w=True)

        for c in self.clients:
            if c.priority >= self.virt.priority:
                raise SubsystemBuildError(
                    f"Client {c} has a priority higher than or equal to virt's "
                    f"({self.virt.priority})!"
                )
            cfg = self.client_gpu_configs[c]

            events_mr, req_mr, resp_mr = self._queue_mrs(
                f"gpu_client_{c.name}", cfg.queue_capacity
            )
            data_mr = MemoryRegion(
                self.sdf,
                f"gpu_client_{c.name}_data",
                self.sdf.arch.roundup_to_page(cfg.data_size),
                physical=True,
            )

            virt_maps = [self.virt.create_automap(mr, rw) for mr in (events_mr, req_mr, resp_mr)]
            client_maps = [c.create_automap(mr, rw) for mr in (events_mr, req_mr, resp_mr)]
            virt_data_map = self.virt.create_automap(data_mr, rw)
            client_data_map = c.create_automap(data_mr, rw)

            ch = Channel(
                self.sdf,
                Channel.End(self.virt, can_notify=True, can_pp=False),
                Channel.End(c, can_notify=True, can_pp=False),
            )

            virt_conn = self.gpu_connection_resource_factory(
                *virt_maps, ch.id_for_pd(self.virt), cfg.queue_capacity
            )
            client_conn = self.gpu_connection_resource_factory(
                *client_maps, ch.id_for_pd(c), cfg.queue_capacity
            )

            self.virt_client_config_protos.append((virt_conn, virt_data_map))
            self.client_config_protos.append((c, client_conn, client_data_map))

    def generate_config_structs(self):
        assert self.driver_config is not None
        assert self.virt_driver_config_proto is not None

        virt_config = self.gpu_virt_config_factory(
            self.virt,
            self.gpu_virt_endpoint_factory(
                "gpu_virt_config_driver_t", *self.virt_driver_config_proto
            ),
            [
                self.gpu_virt_endpoint_factory("gpu_virt_config_client_t", *p)
                for p in self.virt_client_config_protos
            ],
        )
        client_configs = [
            self.gpu_client_config_factory(*p) for p in self.client_config_protos
        ]
        return (
            super().generate_config_structs()
            + [self.driver_config, virt_config]
            + client_configs
        )

    # ### config struct factory functions ###

    def gpu_connection_resource_factory(
        self,
        events_map: Map,
        req_map: Map,
        resp_map: Map,
        ch_id: int,
        num_buffers: int,
    ) -> ConfigStruct:
        fields = {
            "events": RegionResourceFactory(events_map),
            "req_queue": RegionResourceFactory(req_map),
            "resp_queue": RegionResourceFactory(resp_map),
            "num_buffers": num_buffers,
            "id": ch_id,
        }
        return ConfigStruct(fields, "gpu_connection_resource_t")

    def gpu_driver_config_factory(
        self, driver_pd: ProtectionDomain, conn: ConfigStruct, data_map: Map
    ) -> ConfigStruct:
        fields = {
            "magic": GPU_PROTOCOL_MAGIC,
            "virt": conn,
            "data": RegionResourceFactory(data_map),
        }
        return ConfigStruct(
            fields,
            "gpu_driver_config_t",
            target_file=driver_pd.prog_image,
            section_name="gpu_driver_config",
        )

    def gpu_virt_endpoint_factory(
        self, type_name: str, conn: ConfigStruct, data_map: Map
    ) -> ConfigStruct:
        """
        Config telling the virt about one end of a connection (driver or client).
        """
        fields = {
            "conn": conn,
            "data": DeviceRegionResourceFactory(
                RegionResourceFactory(data_map), data_map.mr.paddr
            ),
        }
        return ConfigStruct(fields, type_name)

    def gpu_virt_config_factory(
        self,
        virt_pd: ProtectionDomain,
        driver_config: ConfigStruct,
        client_configs: List[ConfigStruct],
    ) -> ConfigStruct:
        assert len(client_configs) == len(self.clients)
        assert len(client_configs) <= GPU_MAX_CLIENTS
        fields = {
            "magic": GPU_PROTOCOL_MAGIC,
            "num_clients": len(client_configs),
            "driver": driver_config,
            "clients": client_configs,
        }
        return ConfigStruct(
            fields,
            "gpu_virt_config_t",
            target_file=virt_pd.prog_image,
            section_name="gpu_virt_config",
        )

    def gpu_client_config_factory(
        self, client_pd: ProtectionDomain, conn: ConfigStruct, data_map: Map
    ) -> ConfigStruct:
        fields = {
            "magic": GPU_PROTOCOL_MAGIC,
            "virt": conn,
            "data": RegionResourceFactory(data_map),
        }
        return ConfigStruct(
            fields,
            "gpu_client_config_t",
            target_file=client_pd.prog_image,
            section_name="gpu_client_config",
        )


# Tell the driver manifest we exist and that drivers in the gpu tree are usable for us.
register_sddf_subsystem("gpu", sDDFGpu)
