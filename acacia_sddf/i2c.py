# Copyright 2026, UNSW
# SPDX-License-Identifier: BSD-2-Clause

from dataclasses import dataclass
from typing import Tuple

from acacia import (
    Channel,
    ConfigStruct,
    DTBNode,
    Map,
    MemoryRegion,
    ProtectionDomain,
    SchedulingProperties,
    System,
    build_hook,
)

from .driver_manifest import register_sddf_subsystem
from .sddf import RegionResourceFactory, sDDFDriverClass

I2C_PROTOCOL_MAGIC = "sDDF" + chr(0x4)
I2C_CMD_T_SZ = 16  # bytes
I2C_RESPONSE_T_SZ = 16  # bytes
I2C_REQ_Q_T_SZ = 32  # bytes


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


def is_pow_2(x: int):
    return x > 0 and x & (x - 1) == 0


class sDDFI2C(sDDFDriverClass):
    def __init__(
        self,
        sdf: System,
        dev_compatible: str,
        dev_dt_path: str,
        driver_prio: int,
        virt_prio: int,
        cpu: int | None = None,
        virt_elf: str = "i2c_virt.elf",
        driver_elf: str = "i2c_driver.elf",
        req_queue_capacity: int = 128,
        data_size: int | None = None,
    ):
        """
        An instance of an I2C controller (master) driver corresponding to a certain
        interface.

        Args:
            sdf: System - Acacia System to install subsystem to
            dev_compatible: str - device tree compatible string for i2c driver
            dev_dt_path: str    - path to desired i2c interface in device tree blob
            driver_prio: int    - seL4 priority of driver
            virt_prio: int      - seL4 priority of virt
            driver_elf: str     - name of ELF file defining driver
            virt_elf: str       - name of ELF file defining virt
            req_queue_capacity: int     - power-of-2 number of i2c commands that can fit in a queue.
            data_size: int      - power-of-2 size of data MR to back requests. Default to 1 page.

        Since the number of responses in a system is always much smaller than the number of
        requests, we unconditionally squeeze all requests into one page.

        Note: this class assumes a DTB node is available. We do not support non-DTB
              classes currently, but it is WIP.
        """
        # Queue size must be power of two
        if not is_pow_2(req_queue_capacity):
            raise ValueError(
                f"I2C queue size {req_queue_capacity} must be a non-zero power of 2!"
            )

        if data_size is None:
            data_size = sdf.arch.default_page_size_bytes()
        if not is_pow_2(data_size):
            raise ValueError("Data region size must be a power of 2!")
        self.data_size = data_size

        self.sdf = sdf
        self.cpu = cpu
        self.req_queue_capacity = req_queue_capacity

        driver = ProtectionDomain(
            self.sdf,
            "i2c_driver",
            driver_elf,
            scheduling=SchedulingProperties(driver_prio),
            cpu=self.cpu,
        )

        super().__init__(
            sdf, driver, "i2c", dev_compatible, dev_dt_path, magic="sDDF" + chr(0x1)
        )

        # Internal bookkeeping
        self.virt = None
        self.virt_elf = virt_elf

        # Stubs of config structs that we need to collect in construct_infrastructure and connect_clients
        self.virt_config = None
        self.driver_config = None
        self.virt_driver_config = None
        self.client_configs = []

        # Special cases for boards. TODO: remove
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

        self.virt = ProtectionDomain(
            self.sdf,
            "i2c_virt",
            self.virt_elf,
            scheduling=SchedulingProperties(virt_prio),
            cpu=self.cpu,
        )
        # TODO: use dwarfdump to find size of i2c_cmd_t struct manually. Acacia doesn't
        # support this yet. https://github.com/au-ts/microkit_acacia/issues/63

        # i2c_cmd_t is 16 bytes, queue object is 32 bytes. By default (queue_size=128), we
        # want to use one small page only, so this is OK.
        self.req_q_mr_sz = self.sdf.arch.roundup_to_page(
            (I2C_CMD_T_SZ * self.req_queue_capacity) + I2C_REQ_Q_T_SZ
        )

        # Far fewer responses than requests (many i2c_cmds -> one response). Fit as many
        # responses as we can in a default page size.
        # Invariant: both page size and struct size are a power of 2, so this should also be one.
        self.resp_q_mr_sz = self.sdf.arch.default_page_size_bytes()
        num_responses_in_page = self.resp_q_mr_sz // (I2C_RESPONSE_T_SZ)

        # Also need to fit in queue handle. Bin num responses down to nearest pow-2.
        self.resp_queue_capacity = num_responses_in_page >> 1
        assert is_pow_2(self.resp_queue_capacity)

        # Create queues & config for driver
        self.virt_driver_config, driv_virt_conn = self.make_i2c_queues(
            "driver", self.virt, self.driver
        )
        self.driver_config = self.i2c_driver_config_factory(
            self.driver, I2C_PROTOCOL_MAGIC, driv_virt_conn
        )

    def make_i2c_queues(
        self,
        connection_name: str,
        requestor: ProtectionDomain,
        responder: ProtectionDomain,
        allow_pp: bool = False,
    ) -> Tuple[ConfigStruct, ConfigStruct]:
        """
        Create the I2C request and response queue between two PDs, requestor and responder.
        This does NOT make the data region, since those only exist between the client and driver.

        There are only two uses of this function:
            a. Requestor=virt, responder=driver
            b. Requestor=some client, responder = virt

        All objects are named based on the `connection_name` str and thus this must be unique.

        Returns: Tuple (requestor, responder) of i2c_connection_resource config struct for this
                 queue pair.
        """
        # Make queues
        req_q_mr = MemoryRegion(
            self.sdf, f"i2c_request_{connection_name}", self.req_q_mr_sz
        )
        resp_q_mr = MemoryRegion(
            self.sdf, f"i2c_response_{connection_name}", self.resp_q_mr_sz
        )
        responder_req_map = responder.create_automap(req_q_mr, "rw")
        responder_resp_map = responder.create_automap(resp_q_mr, "rw")
        requestor_req_map = requestor.create_automap(req_q_mr, "rw")
        requestor_resp_map = requestor.create_automap(resp_q_mr, "rw")

        ch = Channel(
            self.sdf,
            Channel.End(responder, can_notify=True, can_pp=False),
            Channel.End(requestor, can_notify=True, can_pp=allow_pp),
        )

        # Create config structs
        requestor_conf = self.i2c_connection_resource_factory(
            requestor_req_map,
            requestor_resp_map,
            self.req_queue_capacity,
            self.resp_queue_capacity,
            ch.id_for_pd(requestor),
        )
        responder_conf = self.i2c_connection_resource_factory(
            responder_req_map,
            responder_resp_map,
            self.req_queue_capacity,
            self.resp_queue_capacity,
            ch.id_for_pd(responder),
        )
        return (requestor_conf, responder_conf)

    @build_hook  # Mark this to run when Acacia is performing final steps
    def connect_clients_setup_virt(self):
        assert self.virt is not None
        assert self.driver is not None

        # Clients are connected with:
        # a. request queue
        # b. response queue
        # c. data region shared with driver
        # d. channel for notifications and PPCs
        virt_client_configs = []
        for c in self.clients:
            if c.priority >= self.virt.priority:
                raise SubsystemBuildError(
                    f"Client {c} has a priority higher "
                    f"than virt's ({self.driver.priority})!"
                )
            # Create queues
            client_connection, virt_connection = self.make_i2c_queues(
                c.name, c, self.virt, allow_pp=True
            )

            # Set up data region
            c_data_mr = MemoryRegion(
                self.sdf, f"i2c_client_data_{c.name}", self.data_size
            )
            c_data_map = c.create_automap(c_data_mr, Map.Permissions(r=True, w=True))
            data_map = self.driver.create_automap(
                c_data_mr, Map.Permissions(r=True, w=True)
            )
            client_data = RegionResourceFactory(c_data_map)

            self.client_configs.append(
                self.i2c_client_config_factory(c, client_connection, client_data)
            )
            virt_client_configs.append(
                self.i2c_virt_client_config_factory(
                    virt_connection, self.data_size, data_map.vaddr, c_data_map.vaddr
                )
            )
        # Clients added. Finally, finish setting up virt
        # Virt needs a MR of equal size to the request queue to buffer-in requests while
        # validating them
        virt_intermediary_mr = MemoryRegion(
            self.sdf, "i2c_virt_intermediary", self.req_q_mr_sz
        )
        virt_intermediary_map = self.virt.create_automap(virt_intermediary_mr, "rw")
        self.virt_config = self.i2c_virt_config_factory(
            self.virt,
            I2C_PROTOCOL_MAGIC,
            len(self.clients),
            virt_intermediary_map,
            self.virt_driver_config,
            virt_client_configs,
        )

    def generate_config_structs(self):
        return (
            super().generate_config_structs()
            + [self.driver_config]
            + [self.virt_config]
            + self.client_configs
        )

    # ### dtb utility functions for drivers that depend on i2c ###
    def get_i2c_addresses_from_dtb(self, device_node: DTBNode) -> list[I2CAddress]:
        """
        Try and get the i2c addresses of a device on the bus controlled by this driver.

        If the path given is not for this I2C bus or the device is not present, a
        ValueError will be raised.
        Args:
            device_node: DTBNode - peripheral node
        Returns:
            List[I2CAddress]
        """
        if not self.dtb:
            raise RuntimeError(
                "Cannot get I2C addresses from DTB when system has no DTB!"
            )

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
        self, req_q: Map, resp_q: Map, num_req_bufs: int, num_resp_bufs: int, id: int
    ) -> ConfigStruct:
        fields = {
            "req_queue": RegionResourceFactory(req_q),
            "resp_queue": RegionResourceFactory(resp_q),
            "num_req_buffers": num_req_bufs,
            "num_resp_buffers": num_resp_bufs,
            "id": id,
        }
        return ConfigStruct(fields, type_name="i2c_connection_resource_t")

    def i2c_client_config_factory(
        self,
        client_pd: ProtectionDomain,
        virt_connection: ConfigStruct,
        data_region: ConfigStruct,
    ) -> ConfigStruct:
        """
        Create i2c_client_config for client_pd with serial id n
        """
        fields = {
            "magic": I2C_PROTOCOL_MAGIC,
            "virt": virt_connection,
            "data": data_region,
        }
        return ConfigStruct(
            fields,
            type_name="i2c_client_config_t",
            target_file=client_pd.prog_image,
            section_name="i2c_client_config",
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
        return ConfigStruct(fields, type_name="i2c_virt_client_config_t")

    def i2c_virt_config_factory(
        self,
        virt_pd: ProtectionDomain,
        magic: str,
        num_clients: int,
        intermediary_map: Map,
        driver_connection: ConfigStruct,
        client_connections: list[ConfigStruct],
    ) -> ConfigStruct:
        fields = {
            "magic": magic,
            "num_clients": num_clients,
            "driver": driver_connection,
            "intermediary_mr": RegionResourceFactory(intermediary_map),
            "clients": client_connections,
        }
        return ConfigStruct(
            fields,
            type_name="i2c_virt_config_t",
            target_file=virt_pd.prog_image,
            section_name="i2c_virt_config",
        )

    def i2c_driver_config_factory(
        self, driver_pd: ProtectionDomain, magic: str, virt_connection: ConfigStruct
    ) -> ConfigStruct:
        fields = {
            "magic": magic,
            "virt": virt_connection,
        }
        return ConfigStruct(
            fields,
            type_name="i2c_driver_config_t",
            target_file=driver_pd.prog_image,
            section_name="i2c_driver_config",
        )


# Tell driver manifest we exist and that drivers in the i2c tree are usable for us.
register_sddf_subsystem("i2c", sDDFI2C)
