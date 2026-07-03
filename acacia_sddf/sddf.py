# Copyright 2026, UNSW
# SPDX-License-Identifier: BSD-2-Clause
import sys, os
from typing import List, Optional, Tuple
from abc import abstractmethod
from acacia import (
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
    System,
)
from .driver_manifest import sDDFDriverManifest, sDDFDriverConfig, DTSIRQ, DTSRegion


class sDDFDriverClass(Subsystem):
    """
    This abstract class is inherited by all sDDF driver class implementations.
    It handles:
        a) Mapping of sDDF drivers to their corresponding device tree blobs
        b) Parsing the device tree to set up device resources
        c) Providing some common utility functions for generating config structs, etc.
    """

    def __init__(
        self,
        system: System,
        class_name: str,
        dev_compatible: str,
        dev_dt_path: str,
        magic: str,
    ):
        super().__init__(system, class_name)

        self.sdf = system
        self.dtb = system.dtb
        self.driver_magic = magic
        if system.dtb is None:
            print(
                f"Initialising {class_name} driver with no DTB. Assuming this is x86 and no DTB is needed"
            )
            return

        # Find real DTB node
        print(
            f"Finding {class_name} compatible for {dev_compatible} -- {dev_dt_path} from {self.dtb.file_path}"
        )
        target_node = self.dtb.get_node_by_path(dev_dt_path)

        # make sure compatible matches!
        if dev_compatible not in (a_c := self.dtb.get_compatible(target_node)):
            raise IOError(
                f"Target node {dev_dt_path} has compatible {a_c}... "
                f"doesn't match expected {dev_compatible}!"
            )

        # check if DTB node is "okay" if it has a status
        ok = self.dtb.get_node_prop(target_node, "status")
        if ok is not None and ok.as_str() != "okay":
            raise RuntimeError(f"{target_node} has bad status {ok.as_str()}!")

        self.dtb_node = target_node

        # Find sDDF driver matching this node
        matching_configs = sDDFDriverManifest().get_configs_matching_compatible(
            type(self), dev_compatible
        )

        if len(matching_configs) == 0:
            raise RuntimeError(
                f"No driver config matches {dev_compatible} -> {dev_dt_path}!"
            )
        elif len(matching_configs) != 1:
            raise RuntimeError(
                f"Multiple sDDF drivers satisfy {dev_compatible}! "
                f"There whould be only one.\n{matching_configs}"
            )
        self.driver_config = matching_configs[0]

    def create_dtb_resources(self, driver_pd: ProtectionDomain) -> ConfigStruct:
        """
        Given the driver PD and the DTB+driver_config we were initialised with,
        create all regions, maps, and IRQs required. Creates a DeviceResources ConfigStruct
        for the subsystem to use upon calling `create_config_structs`.

        This method will not run twice; it will return the existing ConfigStruct. I.e.
        there is no risk of creating duplicate MRs, maps or IRQs from this method.

        Args:
            driver_pd: ProtectionDomain
        Returns:
            ConfigStruct -> DeviceResources.
        """
        # Cache DTB regions. Don't want to accidentally make these multiple times.
        if hasattr(self, "__device_resources"):
            return self.__device_resources

        if self.dtb is None:
            print(f"sddf.py: no DTB! Creating dummy device resources.")
            # x86 or otherwise no DTB!
            print("sddf.py: no DTB! Assuming x86")
            self.x86_resources()
            # We generate an empty deviceresources despite it being useless, as our build system expects it.
            self.__device_resources = DeviceResourcesFactory(
                self.driver_magic, [], [], target_file=driver_pd.prog_image
            )
            return self.__device_resources

        region_maps = (
            []
        )  # track fields to store in DeviceResources. tuples of vaddr, offset
        for region in self.driver_config.regions:
            mr = None
            # We name regions as [region_name]_[node_path] to avoid collisions with
            # duplicate driver classes on different nodes
            region_name = region.name + "_" + self.dtb_node.path

            # First: create or find matching MR
            if region.dt_idx is not None:
                # First: find reg property
                regs = self.dtb.get_node_regs(self.dtb_node)
                r_addr, r_sz = regs[region.dt_idx]
                r_sz = self.sdf.arch.roundup_to_page(r_sz)

                # Check we can turn this into a region
                if region.size is not None:
                    if r_sz < region.size:
                        raise RuntimeError()  # todo

                    if (region.size & (self.sdf.arch.default_page_size() - 1)) != 0:
                        raise RuntimeError(
                            f"Region {region} with size={region.size} is not aligned to"
                            f"system page size!"
                        )
                mr_sz = region.size if region.size is not None else r_sz
                d_paddr = self.dtb.get_reg_paddr(self.sdf.arch, self.dtb_node, r_addr)
                d_reg_offset = r_addr % self.sdf.arch.default_page_size()

                # Check if this page is shared (i.e. a matching region is already existing).
                # If regions overlap but don't have the same start, we do nothing and let microkit
                # reject this. Should we reject here? TODO
                existing_mr = [mr for mr in self.sdf.mrs if mr.paddr == d_paddr]
                if len(existing_mr) == 1:
                    mr = existing_mr[0]
                elif len(existing_mr) > 1:
                    raise RuntimeError(
                        f"Multiple MRs with paddr={d_paddr}! -> {existing_mr}"
                    )
                else:
                    # This is new (or overlapping with a different start)
                    mr = MemoryRegion(
                        self.sdf, region_name, mr_sz, paddr=d_paddr, cached=False
                    )
            else:
                # This is a MR that doesn't correspond to physical memory
                # mr = MemoryRegion(region_name, region.size)
                # d_reg_offset = 0

                # If you've run into this, open an issue. Old sdfgen supports this but it seems like a bug.
                raise NotImplementedError("Config region doesn't correspond to DTB!")

            # Second: set up map
            # Assumes permission string is correctly formatted. Non r/w/x chars are ignored
            d_map = driver_pd.create_automap(mr, region.perms if region.perms else "rw")
            region_maps.append((d_map, d_reg_offset))

        # Next: set up IRQs
        irqs_from_prop = self.dtb.get_parsed_irqs(self.dtb_node, self.sdf.arch)
        if len(irqs_from_prop) == 0 and (t := len(self.driver_config.irqs)) != 0:
            raise RuntimeError(
                f"Driver config expects {t} irqs but none found in node!"
            )

        irq_ids = []
        for irq in self.driver_config.irqs:
            dt_irq = irqs_from_prop[irq.dt_index]
            irq_ids.append(driver_pd.add_irq(dt_irq))

        # Finally: make config struct
        self.__device_resources = DeviceResourcesFactory(
            self.driver_magic, region_maps, irq_ids, target_file=driver_pd.prog_image
        )
        return self.__device_resources

    def x86_resources(self):
        """
        Create any resources needed if running on an x86 platform. Automatically
        called in the event that no DTB is present. Subclasses should override this
        method to do whatever they might need.

        By default nothing will happen.
        """
        ...


def RegionResourceFactory(map: Map, section_name: Optional[str] = None, offset=0):
    fields = {"vaddr": map.vaddr + offset, "size": map.mr.size}
    return ConfigStruct("region_resource_t", section_name=section_name, fields=fields)


def DeviceRegionResourceFactory(region: ConfigStruct, io_addr: int):
    fields = {"region": region, "io_addr": io_addr}
    return ConfigStruct("device_region_resource_t", fields=fields)


def DeviceIRQResourceFactory(id: int):
    fields = {"id": id}
    return ConfigStruct("device_irq_resource_t", fields=fields)


def DeviceResourcesFactory(
    magic_str: str,
    maps_offsets: List[Tuple[Map, int]],
    irq_ids: List[int],
    target_file: str,
    section_name="device_resources",
):
    region_structs = [
        DeviceRegionResourceFactory(RegionResourceFactory(m, offset=o), m.mr.paddr)
        for m, o in maps_offsets
    ]
    irq_structs = [DeviceIRQResourceFactory(i) for i in irq_ids]
    fields = {
        "magic": magic_str,
        "num_regions": len(region_structs),
        "num_irqs": len(irq_structs),
        "regions": region_structs,
        "irqs": irq_structs,
    }
    return ConfigStruct(
        "device_resources_t",
        section_name=section_name,
        fields=fields,
        target_file=target_file,
    )
