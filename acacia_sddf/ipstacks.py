# Copyright 2026, UNSW
# SPDX-License-Identifier: BSD-2-Clause

from acacia import ConfigStruct, MemoryRegion, ProtectionDomain, Subsystem, System

from .net import sDDFEthernet
from .sddf import RegionResourceFactory

PBUF_STRUCT_SIZE = 56


class sDDFLWIP(Subsystem):
    def __init__(self, net: sDDFEthernet, target_pd: ProtectionDomain):
        # Sanity: must be same system
        assert target_pd.sdf is net.sdf

        self.net = net
        self.pd = target_pd

        # Disable client list, since we assume that we take our only PD now.
        super().__init__(net.sdf, f"lwip_{target_pd.name}", clients_allowed=False)

        # Automatically call
        self.add_build_hook(self.create_pbuf_pool)

    def create_pbuf_pool(self):
        # We use connect clients to defer allocating a vaddr for the map until after
        # the metaprogram is finished doing config.
        pbuf_pool_mr_sz = self.num_pbufs * PBUF_STRUCT_SIZE
        mr_name = f"{self.net._device_name()}/net/lib_sddf_lwip/{self.pd.name}"
        pbuf_pool = MemoryRegion(self.net.sdf, mr_name, pbuf_pool_mr_sz)
        self.pbuf_map = self.pd.create_automap(pbuf_pool, "rw")

    @property
    def num_pbufs(self) -> int:
        return self.net.rx_buffers * 2

    def generate_config_structs(self) -> list["ConfigStruct"]:
        # Just one struct: lwip config
        return [
            ConfigStruct(
                {
                    "magic": "sDDF" + chr(0x8),
                    "pbuf_pool": RegionResourceFactory(self.pbuf_map),
                    "num_pbufs": self.num_pbufs,
                },
                target_file=self.pd.prog_image,
                section_name="lib_sddf_lwip_config",
                type_name="lib_sddf_lwip_config_t",
            )
        ]
