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
import secrets
from typing import List, Dict, Optional
from dataclasses import dataclass
from .driver_manifest import sDDFDriverManifest, sDDFDriverConfig, DTSIRQ, DTSRegion
from .sddf import (
    sDDFDriverClass,
    DeviceResourcesFactory,
    RegionResourceFactory,
    DeviceRegionResourceFactory,
)


NET_MAGIC = "sDDF" + chr(0x5)
NET_BUFFER_SIZE = 2048


def _is_power_of_two(n: int) -> bool:
    return n > 0 and (n & (n - 1)) == 0


def _next_power_of_two(n: int) -> int:
    return 1 << ((n - 1).bit_length())


@dataclass(frozen=True)
class NetClientOptions:
    rx: bool = True
    rx_buffers: int = 512
    tx: bool = True
    tx_buffers: int = 512
    vswitch: bool = False
    mac_addr: Optional[str] = None


@dataclass
class NetClientInfo:
    rx: bool = True
    rx_buffers: int = 512
    tx: bool = True
    tx_buffers: int = 512
    tx_data: Optional[MemoryRegion] = None
    vswitch: bool = False
    mac_addr: Optional[List[int]] = None


class sDDFEthernet(sDDFDriverClass):

    def __init__(
        self,
        sdf: System,
        dev_compatible: str,
        dev_dt_path: str,
        driver_prio: int,
        virt_tx_prio: int,
        virt_rx_prio: int,
        cpu: Optional[int] = None,
        rx_buffers: int = 512,
        rx_dma_mr: Optional[MemoryRegion] = None,
        virt_tx_elf: str = "net_virt_tx.elf",
        virt_rx_elf: str = "net_virt_rx.elf",
        driver_elf: str = "net_driver.elf",
        # TODO: add automated vswitch handling?
        vswitch: Optional[ProtectionDomain] = None,
    ):
        # The system is designed with the driver at the highest priority,
        # followed by the Tx virtualiser, then the Rx virtualiser.
        assert driver_prio > virt_tx_prio > virt_rx_prio > 0

        self.cpu = cpu
        self.rx_buffers = rx_buffers
        self.rx_dma_mr = rx_dma_mr
        self.vswitch = vswitch

        if rx_dma_mr is not None:
            if rx_dma_mr.paddr is None:
                raise SubsystemBuildError(
                    "rx dma region must have a physical address!"
                )
            if not _is_power_of_two(rx_buffers):
                raise SubsystemBuildError(
                    f"number of rx buffers ({rx_buffers}) must be a power of two!"
                )
            if rx_dma_mr.size < rx_buffers * NET_BUFFER_SIZE:
                raise SubsystemBuildError(
                    "rx dma region must have capacity for all buffers!"
                )

        driver = ProtectionDomain(
            sdf,
            "net_driver",
            driver_elf,
            scheduling=SchedulingProperties(driver_prio, budget=100, period=400),
            cpu=self.cpu,
        )
        super().__init__(
            sdf, driver, "net", dev_compatible, dev_dt_path, magic=NET_MAGIC
        )

        # Parallel to self.clients (from the Subsystem base class).
        self.client_info: List[NetClientInfo] = []
        self.copiers: List[Optional[ProtectionDomain]] = []
        self.copy_config_data: List[Optional[Dict]] = []
        self.copy_configs: List[Optional[ConfigStruct]] = []
        self.client_configs: List[Optional[ConfigStruct]] = []

        # Top-level config structs.
        self.driver_config = None
        self.virt_rx_config = None
        self.virt_tx_config = None
        self.vswitch_config = None

        # Driver <-> virt_rx / virt_tx connections.
        self.driver_config_virt_rx = None
        self.driver_config_virt_tx = None
        self.virt_rx_driver_conn = None
        self.virt_tx_driver_conn = None

        # Deferred pieces for virt_rx (driver/data/metadata + clients).
        self.virt_rx_data_map = None
        self.virt_rx_meta_map = None
        self.virt_rx_client_protos = []
        self.virt_rx_num_clients = 0

        # Deferred pieces for virt_tx (driver conn + clients).
        self.virt_tx_client_protos = []
        self.virt_tx_num_clients = 0

        # Vswitch port data (dicts so we can apply ACL rules before building).
        self.vswitch_port_data: List[Dict] = []
        self.vswitch_num_ports = 0
        self.vswitch_meta_map = None
        self.virt_port = {"rx": None, "tx": None, "tx_data": None}

        self.acl_rules = []

        self.construct_infrastructure(virt_tx_prio, virt_rx_prio, virt_tx_elf, virt_rx_elf)

    def construct_infrastructure(
        self, virt_tx_prio: int, virt_rx_prio: int, virt_tx_elf: str, virt_rx_elf: str
    ):
        self.virt_tx = ProtectionDomain(
            self.sdf,
            "net_virt_tx",
            virt_tx_elf,
            scheduling=SchedulingProperties(virt_tx_prio, budget=20000),
            cpu=self.cpu,
        )
        self.virt_rx = ProtectionDomain(
            self.sdf,
            "net_virt_rx",
            virt_rx_elf,
            scheduling=SchedulingProperties(virt_rx_prio),
            cpu=self.cpu,
        )

    # ### public API ###

    def add_client(
        self,
        client: ProtectionDomain,
        copier: Optional[ProtectionDomain] = None,
        rx: bool = NetClientOptions.rx,
        rx_buffers: int = NetClientOptions.rx_buffers,
        tx: bool = NetClientOptions.tx,
        tx_buffers: int = NetClientOptions.tx_buffers,
        vswitch_client: bool = NetClientOptions.vswitch,
        mac_addr: Optional[str] = NetClientOptions.mac_addr,
    ):
        # A vswitch client requires a vswitch PD.
        if vswitch_client and self.vswitch is None:
            raise SubsystemBuildError(
                f"Client {client.name} is a vswitch client but no vswitch "
                f"PD was provided to {type(self).__name__}"
            )
        # A vswitch client must have a copier.
        if vswitch_client and copier is None:
            raise SubsystemBuildError(
                f"Client {client.name} is a vswitch client and must have a copier"
            )
        # Vswitch clients must support both rx and tx.
        if vswitch_client and (not rx or not tx):
            raise SubsystemBuildError(
                f"Vswitch client {client.name} must support both rx and tx"
            )
        # At least rx or tx must be enabled.
        if not rx and not tx:
            raise SubsystemBuildError(
                f"Client {client.name} must have at least rx or tx enabled"
            )
        # Number of client buffers must each be a power of two.
        if tx and not _is_power_of_two(tx_buffers):
            raise SubsystemBuildError(
                f"Client {client.name}: tx buffer count ({tx_buffers}) "
                f"is not a power of two"
            )
        if rx and copier is not None and not _is_power_of_two(rx_buffers):
            raise SubsystemBuildError(
                f"Client {client.name}: rx buffer count ({rx_buffers}) "
                f"is not a power of two"
            )

        parsed_mac = None
        if mac_addr is not None:
            parsed_mac = self._parse_mac_addr(mac_addr)
            for existing in self.client_info:
                if existing.mac_addr == parsed_mac:
                    raise SubsystemBuildError(
                        f"MAC address {mac_addr} already in use"
                    )

        for existing in self.clients:
            if existing.name == client.name:
                raise SubsystemBuildError(
                    f"Client with name {client.name} already exists"
                )
        if copier is not None:
            for existing in self.copiers:
                if existing is not None and existing.name == copier.name:
                    raise SubsystemBuildError(
                        f"Copier with name {copier.name} already exists"
                    )

        super().add_client(client)
        idx = len(self.clients) - 1
        self.client_info.append(NetClientInfo())
        self.copiers.append(copier)
        self.copy_config_data.append(None)
        self.copy_configs.append(None)
        self.client_configs.append(None)

        info = self.client_info[idx]
        # Without a copier the number of rx buffers must equal the number of dma buffers.
        info.rx_buffers = rx_buffers if copier is not None else self.rx_buffers
        info.tx_buffers = tx_buffers
        info.rx = rx
        info.tx = tx
        info.vswitch = vswitch_client
        info.mac_addr = parsed_mac

    def add_acl_rule(
        self,
        client0: ProtectionDomain,
        client1: ProtectionDomain,
        zero_to_one: bool = True,
        one_to_zero: bool = True,
    ):
        if self.vswitch is None:
            raise SubsystemBuildError(
                "Cannot add an ACL rule without a vswitch in the system"
            )
        if client0.name == client1.name:
            raise SubsystemBuildError(
                "Cannot add an ACL rule between a client and itself"
            )
        self.acl_rules.append((client0.name, client1.name, zero_to_one, one_to_zero))

    # ### connection phase ###

    def connect_clients(self):
        if len(self.clients) == 0:
            raise SubsystemBuildError(
                "Cannot connect an ethernet subsystem with no clients"
            )

        rx_dma_mr = self.rx_connect_driver()
        self.tx_connect_driver()
        self._generate_mac_addrs()

        num_vswitch_clients = sum(1 for i in self.client_info if i.vswitch)
        num_vswitch_client_buffers = sum(
            i.tx_buffers for i in self.client_info if i.vswitch
        )

        for idx, client in enumerate(self.clients):
            info = self.client_info[idx]
            rx_conn = None
            rx_data_map = None
            tx_conn = None
            tx_data_map = None

            if info.vswitch:
                rx_conn, rx_data_map, vswitch_rx_conn = self.client_rx_vswitch_connect(
                    idx, num_vswitch_clients
                )
                tx_conn, tx_data_map, vswitch_tx_conn, vswitch_tx_data_map = (
                    self.client_tx_vswitch_connect(idx)
                )
                self.vswitch_port_data.append(
                    {
                        "rx_conn": vswitch_rx_conn,
                        "tx_conn": vswitch_tx_conn,
                        "tx_data_map": vswitch_tx_data_map,
                        "mac_addr": info.mac_addr,
                        "acl": 0,
                    }
                )
                self.vswitch_num_ports += 1
            else:
                if info.rx:
                    rx_conn, rx_data_map, virt_rx_conn = self.client_rx_connect(idx)
                    self.virt_rx_client_protos.append(
                        (virt_rx_conn, [info.mac_addr], 1)
                    )
                    self.virt_rx_num_clients += 1
                if info.tx:
                    tx_conn, tx_data_map, virt_tx_conn, virt_tx_data_map = (
                        self.client_tx_connect(idx)
                    )
                    self.virt_tx_client_protos.append(
                        (virt_tx_conn, [(virt_tx_data_map, info.tx_buffers)], 1)
                    )
                    self.virt_tx_num_clients += 1

            self.client_configs[idx] = self.net_client_config_factory(
                client,
                NET_MAGIC,
                rx_conn,
                rx_data_map,
                tx_conn,
                tx_data_map,
                info.mac_addr,
            )

        if self.vswitch is not None:
            self.vswitch_rx_connect(rx_dma_mr, num_vswitch_client_buffers + self.rx_buffers)
            self.vswitch_tx_connect(num_vswitch_client_buffers)

            # The final (virtualiser) port: mac is ignored.
            self.vswitch_port_data.append(
                {
                    "rx_conn": self.virt_port["rx"],
                    "tx_conn": self.virt_port["tx"],
                    "tx_data_map": self.virt_port["tx_data"],
                    "mac_addr": [0, 0, 0, 0, 0, 0],
                    "acl": 0,
                }
            )
            self.vswitch_num_ports += 1

            self._apply_acl_rules()
            ports = [
                self.net_vswitch_port_config_factory(**d) for d in self.vswitch_port_data
            ]
            self.vswitch_config = self.net_vswitch_config_factory(
                ports, self.vswitch_num_ports, self.vswitch_meta_map
            )

        self.driver_config = self.net_driver_config_factory(
            self.driver_config_virt_rx, self.driver_config_virt_tx
        )

        # Build the copy configs now that all rx_data entries are known.
        for idx, data in enumerate(self.copy_config_data):
            if data is None:
                continue
            rx_data_regions = self._rx_data_regions(data["rx_data"])
            self.copy_configs[idx] = self.net_copy_config_factory(
                self.copiers[idx],
                NET_MAGIC,
                data["rx_conn"],
                rx_data_regions,
                data["client_conn"],
                data["client_data_map"],
            )

    # ### per-connection helpers ###

    def rx_connect_driver(self):
        driver_conn, virt_rx_conn = self.create_connection(
            self.driver, self.virt_rx, self.rx_buffers, server_pp=False
        )
        self.driver_config_virt_rx = driver_conn
        self.virt_rx_driver_conn = virt_rx_conn

        if self.rx_dma_mr is None:
            rx_dma_size = self.sdf.arch.roundup_to_page(
                self.rx_buffers * NET_BUFFER_SIZE
            )
            self.rx_dma_mr = MemoryRegion(
                self.sdf,
                f"{self._device_name()}/net/rx/data/device",
                rx_dma_size,
                physical=True,
            )

        # The Rx virtualiser maps the DMA region read-only for its data region.
        self.virt_rx_data_map = self.virt_rx.create_automap(self.rx_dma_mr, "r")

        # Reference-count metadata region for the Rx virtualiser.
        meta_size = self.sdf.arch.roundup_to_page(self.rx_buffers)
        meta_mr = MemoryRegion(
            self.sdf, f"{self._device_name()}/net/rx/virt_metadata", meta_size
        )
        self.virt_rx_meta_map = self.virt_rx.create_automap(meta_mr, "rw")

        return self.rx_dma_mr

    def tx_connect_driver(self):
        num_buffers = sum(
            i.tx_buffers for i in self.client_info if i.tx
        )
        driver_conn, virt_tx_conn = self.create_connection(
            self.driver, self.virt_tx, num_buffers, server_pp=False
        )
        self.driver_config_virt_tx = driver_conn
        self.virt_tx_driver_conn = virt_tx_conn

    def client_rx_connect(self, idx: int):
        client = self.clients[idx]
        info = self.client_info[idx]
        copier = self.copiers[idx]
        dev = self._device_name()

        if copier is not None:
            virt_rx_conn, copier_rx_conn = self.create_connection(
                self.virt_rx, copier, self.rx_buffers, server_pp=False
            )
            copier_client_conn, client_rx_conn = self.create_connection(
                copier, client, info.rx_buffers, server_pp=False
            )

            rx_dma_copier_map = copier.create_automap(self.rx_dma_mr, "rw")

            client_data_size = self.sdf.arch.roundup_to_page(
                self.rx_buffers * NET_BUFFER_SIZE
            )
            client_data_mr = MemoryRegion(
                self.sdf,
                f"{dev}/net/rx/data/client/{client.name}",
                client_data_size,
            )
            client_data_client_map = client.create_automap(client_data_mr, "rw")
            client_data_copier_map = copier.create_automap(client_data_mr, "rw")

            self.copy_config_data[idx] = {
                "rx_conn": copier_rx_conn,
                "rx_data": {0: rx_dma_copier_map},
                "client_conn": copier_client_conn,
                "client_data_map": client_data_copier_map,
            }
            return client_rx_conn, client_data_client_map, virt_rx_conn
        else:
            # Trusted/direct client talks straight to the Rx virtualiser.
            virt_rx_conn, client_rx_conn = self.create_connection(
                self.virt_rx, client, self.rx_buffers, server_pp=False
            )
            rx_dma_client_map = client.create_automap(self.rx_dma_mr, "rw")
            return client_rx_conn, rx_dma_client_map, virt_rx_conn

    def client_tx_connect(self, idx: int):
        client = self.clients[idx]
        info = self.client_info[idx]
        dev = self._device_name()

        virt_tx_conn, client_tx_conn = self.create_connection(
            self.virt_tx, client, info.tx_buffers, server_pp=False
        )

        data_mr_size = self.sdf.arch.roundup_to_page(info.tx_buffers * NET_BUFFER_SIZE)
        data_mr = MemoryRegion(
            self.sdf,
            f"{dev}/net/tx/data/client/{client.name}",
            data_mr_size,
            physical=True,
        )
        info.tx_data = data_mr

        # The Tx virtualiser maps the client's DMA region read-only for cache ops.
        data_mr_virt_map = self.virt_tx.create_automap(data_mr, "r")
        data_mr_client_map = client.create_automap(data_mr, "rw")
        return client_tx_conn, data_mr_client_map, virt_tx_conn, data_mr_virt_map

    def client_rx_vswitch_connect(self, idx: int, num_vswitch_clients: int):
        client = self.clients[idx]
        info = self.client_info[idx]
        copier = self.copiers[idx]
        dev = self._device_name()

        vswitch_rx_conn, copier_rx_conn = self.create_connection(
            self.vswitch, copier, self.rx_buffers, server_pp=False
        )
        copier_client_conn, client_rx_conn = self.create_connection(
            copier, client, info.rx_buffers, server_pp=False
        )

        rx_dma_copier_map = copier.create_automap(self.rx_dma_mr, "rw")

        client_data_size = self.sdf.arch.roundup_to_page(
            self.rx_buffers * NET_BUFFER_SIZE
        )
        client_data_mr = MemoryRegion(
            self.sdf,
            f"{dev}/net/rx/data/client/{client.name}",
            client_data_size,
        )
        client_data_client_map = client.create_automap(client_data_mr, "rw")
        client_data_copier_map = copier.create_automap(client_data_mr, "rw")

        # The Rx DMA region is the last data region slot for a vswitch copier.
        self.copy_config_data[idx] = {
            "rx_conn": copier_rx_conn,
            "rx_data": {num_vswitch_clients: rx_dma_copier_map},
            "client_conn": copier_client_conn,
            "client_data_map": client_data_copier_map,
        }
        return client_rx_conn, client_data_client_map, vswitch_rx_conn

    def client_tx_vswitch_connect(self, idx: int):
        client = self.clients[idx]
        info = self.client_info[idx]
        dev = self._device_name()

        vswitch_tx_conn, client_tx_conn = self.create_connection(
            self.vswitch, client, info.tx_buffers, server_pp=True
        )

        data_mr_size = self.sdf.arch.roundup_to_page(info.tx_buffers * NET_BUFFER_SIZE)
        data_mr = MemoryRegion(
            self.sdf,
            f"{dev}/net/tx/data/client/{client.name}",
            data_mr_size,
            physical=True,
        )
        info.tx_data = data_mr

        data_mr_vswitch_map = self.vswitch.create_automap(data_mr, "rw")
        data_mr_client_map = client.create_automap(data_mr, "rw")
        return (
            client_tx_conn,
            data_mr_client_map,
            vswitch_tx_conn,
            data_mr_vswitch_map,
        )

    def vswitch_rx_connect(self, rx_dma_mr: MemoryRegion, num_vswitch_buffers: int):
        dev = self._device_name()

        virt_rx_conn, vswitch_rx_conn = self.create_connection(
            self.virt_rx, self.vswitch, self.rx_buffers, server_pp=False
        )

        # The vswitch appears to the Rx virtualiser as a client with the MACs of
        # all its vswitch clients.
        vswitch_macs = [info.mac_addr for info in self.client_info if info.vswitch]
        self.virt_rx_client_protos.append((virt_rx_conn, vswitch_macs, len(vswitch_macs)))
        self.virt_rx_num_clients += 1

        # Reference-count metadata region for the vswitch.
        meta_size = self.sdf.arch.roundup_to_page(num_vswitch_buffers)
        meta_mr = MemoryRegion(self.sdf, f"{dev}/net/vswitch/metadata", meta_size)
        self.vswitch_meta_map = self.vswitch.create_automap(meta_mr, "rw")

        # The device Rx DMA region is mapped into the vswitch as its tx_data.
        rx_dma_vswitch_map = self.vswitch.create_automap(rx_dma_mr, "r")

        # Map each vswitch client's Tx data region into every other vswitch
        # client's copier (read-only).
        for i, _ in enumerate(self.clients):
            if self.client_info[i].vswitch:
                for j, copier in enumerate(self.copiers):
                    if (
                        copier is not None
                        and self.client_info[j].vswitch
                        and i != j
                    ):
                        tx_mr = self.client_info[i].tx_data
                        copier_map = copier.create_automap(tx_mr, "r")
                        self.copy_config_data[j]["rx_data"][i] = copier_map

        # port.tx corresponds to the Rx virtualiser connection (see config.h).
        self.virt_port["tx"] = vswitch_rx_conn
        self.virt_port["tx_data"] = rx_dma_vswitch_map

    def vswitch_tx_connect(self, num_vswitch_client_buffers: int):
        virt_tx_conn, vswitch_tx_conn = self.create_connection(
            self.virt_tx, self.vswitch, num_vswitch_client_buffers, server_pp=False
        )

        regions = []
        for i, _ in enumerate(self.clients):
            if self.client_info[i].vswitch:
                tx_mr = self.client_info[i].tx_data
                virt_tx_client_map = self.virt_tx.create_automap(tx_mr, "r")
                regions.append((virt_tx_client_map, self.client_info[i].tx_buffers))
        self.virt_tx_client_protos.append((virt_tx_conn, regions, len(regions)))
        self.virt_tx_num_clients += 1

        # port.rx corresponds to the Tx virtualiser connection (see config.h).
        self.virt_port["rx"] = vswitch_tx_conn

    # ### MAC address helpers ###

    def _parse_mac_addr(self, mac_str: str) -> List[int]:
        parts = mac_str.split(":")
        if len(parts) != 6:
            raise SubsystemBuildError(f"Invalid MAC address: {mac_str}")
        try:
            return [int(p, 16) for p in parts]
        except ValueError:
            raise SubsystemBuildError(f"Invalid MAC address: {mac_str}")

    def _random_mac(self) -> List[int]:
        mac = [secrets.randbits(8) for _ in range(6)]
        # Set the locally administered bit.
        mac[0] |= 1 << 1
        # Ensure it is an individual (unicast) address.
        mac[0] &= 0b11111110
        return mac

    def _generate_mac_addrs(self):
        for info in self.client_info:
            if info.mac_addr is None:
                mac = self._random_mac()
                while mac in [e.mac_addr for e in self.client_info if e.mac_addr is not None]:
                    mac = self._random_mac()
                info.mac_addr = mac

    def _apply_acl_rules(self):
        for client0_name, client1_name, zero_to_one, one_to_zero in self.acl_rules:
            p0 = None
            p1 = None
            port = 0
            for idx, client in enumerate(self.clients):
                if self.client_info[idx].vswitch:
                    if client.name == client0_name:
                        p0 = port
                    elif client.name == client1_name:
                        p1 = port
                    port += 1
            # A "virt" client matches the (last) virtualiser port.
            if p0 is None and "virt" in client0_name:
                p0 = self.vswitch_num_ports - 1
            elif p1 is None and "virt" in client1_name:
                p1 = self.vswitch_num_ports - 1
            if p0 is None or p1 is None:
                raise SubsystemBuildError(
                    f"Could not resolve ACL rule between {client0_name} and {client1_name}"
                )
            if zero_to_one:
                self.vswitch_port_data[p0]["acl"] |= 1 << p1
            else:
                self.vswitch_port_data[p0]["acl"] &= ~(1 << p1)
            if one_to_zero:
                self.vswitch_port_data[p1]["acl"] |= 1 << p0
            else:
                self.vswitch_port_data[p1]["acl"] &= ~(1 << p0)

    # ### generic helpers ###

    def _device_name(self) -> str:
        node = getattr(self, "dtb_node", None)
        return node.name if node is not None else "generic"

    def create_connection(
        self,
        server: ProtectionDomain,
        client: ProtectionDomain,
        num_buffers: int,
        server_pp: bool,
    ):
        # Queues must always be a power of two.
        rounded = _next_power_of_two(num_buffers)
        queue_mr_size = self.sdf.arch.roundup_to_page(8 + 16 * rounded)
        dev = self._device_name()

        free_mr = MemoryRegion(
            self.sdf,
            f"{dev}/net/queue/{server.name}/{client.name}/free",
            queue_mr_size,
        )
        server_free = server.create_automap(free_mr, "rw")
        client_free = client.create_automap(free_mr, "rw")

        active_mr = MemoryRegion(
            self.sdf,
            f"{dev}/net/queue/{server.name}/{client.name}/active",
            queue_mr_size,
        )
        server_active = server.create_automap(active_mr, "rw")
        client_active = client.create_automap(active_mr, "rw")

        ch = Channel(
            self.sdf,
            Channel.End(server, can_notify=True, can_pp=server_pp),
            Channel.End(client, can_notify=True, can_pp=False),
        )

        server_conn = self.net_connection_resource_factory(
            server_free, server_active, ch.id_for_pd(server), rounded
        )
        client_conn = self.net_connection_resource_factory(
            client_free, client_active, ch.id_for_pd(client), rounded
        )
        return server_conn, client_conn

    # ### deferred config assembly (needs assigned paddrs) ###

    def generate_config_structs(self):
        virt_rx_clients = [
            self.net_virt_rx_client_config_factory(*proto)
            for proto in self.virt_rx_client_protos
        ]
        self.virt_rx_config = self.net_virt_rx_config_factory(
            self.virt_rx_driver_conn,
            self.virt_rx_data_map,
            self.virt_rx_meta_map,
            virt_rx_clients,
            self.virt_rx_num_clients,
        )

        virt_tx_clients = [
            self.net_virt_tx_client_config_factory(*proto)
            for proto in self.virt_tx_client_protos
        ]
        self.virt_tx_config = self.net_virt_tx_config_factory(
            self.virt_tx_driver_conn,
            virt_tx_clients,
            self.virt_tx_num_clients,
        )

        configs = [self.driver_config, self.virt_rx_config, self.virt_tx_config]
        if self.vswitch is not None:
            configs.append(self.vswitch_config)
        configs += self.copy_configs
        configs += self.client_configs

        return super().generate_config_structs() + configs

    # ### config struct factory functions ###

    def net_connection_resource_factory(
        self,
        free_queue_map: Map,
        active_queue_map: Map,
        ch_id: int,
        num_buffers: int,
    ) -> ConfigStruct:
        fields = {
            "free_queue": RegionResourceFactory(free_queue_map),
            "active_queue": RegionResourceFactory(active_queue_map),
            "num_buffers": num_buffers,
            "id": ch_id,
        }
        return ConfigStruct("net_connection_resource_t", fields=fields)

    def net_driver_config_factory(
        self, virt_rx_conn: ConfigStruct, virt_tx_conn: ConfigStruct
    ) -> ConfigStruct:
        fields = {
            "magic": NET_MAGIC,
            "virt_rx": virt_rx_conn,
            "virt_tx": virt_tx_conn,
        }
        return ConfigStruct(
            "net_driver_config_t",
            target_file=self.driver.prog_image,
            section_name="net_driver_config",
            fields=fields,
        )

    def net_virt_rx_client_config_factory(
        self, conn: ConfigStruct, mac_addrs: List[List[int]], num_macs: int
    ) -> ConfigStruct:
        fields = {
            "conn": conn,
            "mac_addrs": mac_addrs,
            "num_macs": num_macs,
        }
        return ConfigStruct("net_virt_rx_client_config_t", fields=fields)

    def net_virt_rx_config_factory(
        self,
        driver_conn: ConfigStruct,
        data_map: Map,
        buffer_meta_map: Map,
        clients: List[ConfigStruct],
        num_clients: int,
    ) -> ConfigStruct:
        fields = {
            "magic": NET_MAGIC,
            "driver": driver_conn,
            "data": DeviceRegionResourceFactory(
                RegionResourceFactory(data_map), data_map.mr.paddr
            ),
            "buffer_metadata": RegionResourceFactory(buffer_meta_map),
            "clients": clients,
            "num_clients": num_clients,
        }
        return ConfigStruct(
            "net_virt_rx_config_t",
            target_file=self.virt_rx.prog_image,
            section_name="net_virt_rx_config",
            fields=fields,
        )

    def net_virt_tx_client_config_factory(
        self, conn: ConfigStruct, regions: List, num_regions: int
    ) -> ConfigStruct:
        # regions is a list of (data_map, num_buffers) tuples. The data map's
        # paddr is assigned at assembly time, hence deferred assembly here.
        region_structs = []
        for data_map, num_buffers in regions:
            region_structs.append(
                ConfigStruct(
                    "net_virt_tx_data_region_t",
                    fields={
                        "data": DeviceRegionResourceFactory(
                            RegionResourceFactory(data_map), data_map.mr.paddr
                        ),
                        "num_buffers": num_buffers,
                    },
                )
            )
        fields = {
            "conn": conn,
            "regions": region_structs,
            "num_regions": num_regions,
        }
        return ConfigStruct("net_virt_tx_client_config_t", fields=fields)

    def net_virt_tx_config_factory(
        self,
        driver_conn: ConfigStruct,
        clients: List[ConfigStruct],
        num_clients: int,
    ) -> ConfigStruct:
        fields = {
            "magic": NET_MAGIC,
            "driver": driver_conn,
            "clients": clients,
            "num_clients": num_clients,
        }
        return ConfigStruct(
            "net_virt_tx_config_t",
            target_file=self.virt_tx.prog_image,
            section_name="net_virt_tx_config",
            fields=fields,
        )

    def net_vswitch_port_config_factory(
        self, rx_conn, tx_conn, tx_data_map, mac_addr, acl
    ) -> ConfigStruct:
        fields = {
            "rx": rx_conn,
            "tx": tx_conn,
            "tx_data": RegionResourceFactory(tx_data_map),
            "mac_addr": mac_addr,
            "acl": acl,
        }
        return ConfigStruct("net_vswitch_port_config_t", fields=fields)

    def net_vswitch_config_factory(
        self,
        ports: List[ConfigStruct],
        num_ports: int,
        buffer_meta_map: Map,
    ) -> ConfigStruct:
        fields = {
            "magic": NET_MAGIC,
            "ports": ports,
            "num_ports": num_ports,
            "buffer_metadata": RegionResourceFactory(buffer_meta_map),
        }
        return ConfigStruct(
            "net_vswitch_config_t",
            target_file=self.vswitch.prog_image,
            section_name="net_vswitch_config",
            fields=fields,
        )

    def net_copy_config_factory(
        self,
        copier_pd: ProtectionDomain,
        magic: str,
        rx_conn: ConfigStruct,
        rx_data_regions: List[ConfigStruct],
        client_conn: ConfigStruct,
        client_data_map: Map,
    ) -> ConfigStruct:
        fields = {
            "magic": magic,
            "rx": rx_conn,
            "rx_data": rx_data_regions,
            "client": client_conn,
            "client_data": RegionResourceFactory(client_data_map),
        }
        return ConfigStruct(
            "net_copy_config_t",
            target_file=copier_pd.prog_image,
            section_name="net_copy_config",
            fields=fields,
        )

    def net_client_config_factory(
        self,
        client_pd: ProtectionDomain,
        magic: str,
        rx_conn: Optional[ConfigStruct],
        rx_data_map: Optional[Map],
        tx_conn: Optional[ConfigStruct],
        tx_data_map: Optional[Map],
        mac_addr: List[int],
    ) -> ConfigStruct:
        # Inactive directions are zeroed so the C struct remains complete.
        rx_conn = rx_conn if rx_conn is not None else ConfigStruct({}, empty=True)
        tx_conn = tx_conn if tx_conn is not None else ConfigStruct({}, empty=True)
        rx_data = (
            RegionResourceFactory(rx_data_map)
            if rx_data_map is not None
            else ConfigStruct({}, empty=True)
        )
        tx_data = (
            RegionResourceFactory(tx_data_map)
            if tx_data_map is not None
            else ConfigStruct({}, empty=True)
        )
        fields = {
            "magic": magic,
            "rx": rx_conn,
            "rx_data": rx_data,
            "tx": tx_conn,
            "tx_data": tx_data,
            "mac_addr": mac_addr,
        }
        return ConfigStruct(
            "net_client_config_t",
            target_file=client_pd.prog_image,
            section_name="net_client_config",
            fields=fields,
        )

    # ### misc helpers ###
    def _rx_data_regions(self, rx_data: Dict[int, Map]) -> List[ConfigStruct]:
        """Expand a {slot: map} dict into an array of region resources."""
        if not rx_data:
            return []
        max_slot = max(rx_data.keys())
        regions = []
        for slot in range(max_slot + 1):
            if slot in rx_data:
                regions.append(RegionResourceFactory(rx_data[slot]))
            else:
                regions.append(ConfigStruct({}, empty=True))
        return regions

    def x86_resources(self):
        # Nothing needed for now?
        ...

def add_driver_config(driver_name: str, config: sDDFDriverConfig):
    sDDFDriverManifest().add_driver_config(sDDFEthernet, driver_name, config)

add_driver_config(
    "meson",
    sDDFDriverConfig(
        compatible="amlogic,meson-g12a-dwmac",
        regions=[DTSRegion("regs", "rw", 4096, 0)],
        irqs=[DTSIRQ(0)],
    ),
)
