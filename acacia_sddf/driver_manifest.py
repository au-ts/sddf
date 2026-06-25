# Copyright 2026, UNSW
# SPDX-License-Identifier: BSD-2-Clause

from dataclasses import dataclass
from typing import List, Dict, Type, Union, Optional
from collections import defaultdict

@dataclass
class DTSRegion:
    name: str
    perms: str = None
    size: int = None
    dt_idx: int = None

@dataclass
class DTSIRQ:
    dt_index: int

@dataclass
class sDDFDriverConfig:
    """
    Encapsulation of device tree fields describing an instance
    of a driver.

    WARNING: the order of regions and irqs affects the order they are
    mapped into the driver in config structs! We REALLY shouldn't have
    this be the case. This is a hangover from `config.json` and sdfgen.

    TODO: make this better in future
    """
    compatible: Union[List[str], str]
    regions: List[DTSRegion]
    irqs: List[DTSIRQ]
    def __post_init__(self):
        if type(self.compatible) is str:
            self.compatible = [self.compatible]
        assert type(self.regions) is list
        assert type(self.irqs) is list


class __sDDFDriverManifest:
    """
    Wrapper class encapsulating sDDF driver manifest. This is a
    mapping of driver subsystem type -> list of driver names ->
    DTS fields. I.e. this encodes:
        * Which drivers are compatible with what devices, according to the
          device tree,
        * What drivers are available in each driver class,
        * Which driver subsystem types in sdfgen map to which drivers.

    You should NOT make a new instance of this class! Use the
    `sDDFDriverManifest()` function to get the global instance.
    """
    def __init__(self):
        self.map: Dict[Type[sDDFDeviceClass], Dict[str, sDDFDriverConfig]] = defaultdict(dict)

    def add_driver_config(self,
                          subsystem_type: Type[sDDFDriverConfig],
                          driver_name: str,
                          config: sDDFDriverConfig):
        # Refuse namespace collisions
        if driver_name in self.map[subsystem_type]:
            raise ValueError(f"Driver named {driver_name} already exists for "
                             f"{subsystem_type}!")
        self.map[subsystem_type][driver_name] = config

    def __getitem__(self, item):
        # Allow array syntax for indexing into dict of driver names per class type
        return self.map[item]

    def get_configs_matching_compatible(self, subsystem_type: Type[sDDFDriverConfig], compat: str) -> List[sDDFDriverConfig]:
        return [c for c in self.map[subsystem_type].values() if compat in c.compatible]

module_manifest = __sDDFDriverManifest()

def sDDFDriverManifest():
    return module_manifest


