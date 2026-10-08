# Copyright 2026, UNSW
# SPDX-License-Identifier: BSD-2-Clause

import json
import os
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path
from typing import Optional

_MODULE_DIR = Path(__file__).resolve().parent
_DRIVERS_DIR = _MODULE_DIR.parent / "drivers"
_CACHE_FILE = _MODULE_DIR / "sddf_driver_config_cache.json"
_CACHE_VERSION = 1


@dataclass
class DTSRegion:
    name: str
    perms: Optional[str] = None
    size: Optional[int] = None
    dt_idx: Optional[int] = None
    cached: bool = False


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

    compatible: list[str] | str
    regions: list[DTSRegion]
    irqs: list[DTSIRQ]

    def __post_init__(self):
        if isinstance(self.compatible, str):
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

    This scans the sDDF for `config.json` files and matches them to Acacia
    classes which have registered themselves with register_sddf_subsystem.

    A cache file is kept to prevent needing to scan the whole tree every build.

    You should NOT make a new instance of this class! Use the
    `sDDFDriverManifest()` function to get the global instance.
    """

    def __init__(self):
        self.map: dict[type["sDDFDriverClass"], dict[str, sDDFDriverConfig]] = (
            defaultdict(dict)
        )

        # Mapping of driver directories -> Acacia class type
        self.subsystems: dict[str, type["sDDFDriverClass"]] = {}

        # Populate from cache if possible; otherwise scan the tree.
        configs = self._read_cache()
        if configs is None:
            configs = self._scan_drivers()
            try:
                self._write_cache(configs)
            except OSError as e:
                print(f"WARNING: couldn't write driver cache to disk due to {e}")

        # config.jsons keyed by dir
        self._configs = configs
        self._materialise()

    def __getitem__(self, item):
        return self.map[item]

    def get_configs_matching_compatible(
        self, subsystem_type: type["sDDFDriverClass"], compat: str
    ) -> list[sDDFDriverConfig]:
        matches = [
            config
            for config in self.__getitem__(subsystem_type).values()
            if compat in config.compatible
        ]
        if not matches:
            # A new driver has appeared or this is missing. Rescan.
            self.rescan()
        return matches

    def register_subsystem(
        self, subsystem_name: str, driver_class: type["sDDFDriverClass"]
    ):
        existing = self.subsystems.get(subsystem_name)
        if existing is not None:
            if existing is not driver_class:
                raise ValueError(
                    f"Subsystem {subsystem_name} already registered to {existing}!"
                )
            return
        self.subsystems[subsystem_name] = driver_class
        self.rescan()

    def rescan(self):
        """
        Scan the drivers tree, rewrite the cache file, and rebuild
        self.map.
        """
        configs = self._scan_drivers()
        try:
            self._write_cache(configs)
        except OSError as e:
            print(f"WARNING: Failed to write cache file due to {e}!")
        self._configs = configs
        self._materialise()

    def _scan_drivers(self) -> dict:
        """
        Find every config.json under the drivers tree. Returns the raw
        JSON documents keyed "<subsystem>/<driver>", where the driver
        name is the full directory path under its subsystem (excluding the
        subsystem name itself).
        """
        configs: dict = {}
        if not _DRIVERS_DIR.is_dir():
            return configs
        for path in sorted(_DRIVERS_DIR.rglob("config.json")):
            rel = path.relative_to(_DRIVERS_DIR)
            if len(rel.parts) < 2:
                raise ValueError(
                    f"unexpected driver layout at {rel}; expected "
                    f"drivers/<subsystem>/.../config.json"
                )
            subsystem_name = rel.parts[0]
            # Everything between the subsystem and config.json is the driver path.
            driver_name = "/".join(rel.parts[1:-1])
            key = f"{subsystem_name}/{driver_name}"
            try:
                document = json.loads(path.read_text(encoding="utf-8"))
                self._parse_config_json(document)  # validate as we go
            except (OSError, ValueError, KeyError, TypeError) as e:
                raise ValueError(f"invalid driver config at drivers/{key}: {e}") from e
            configs[key] = document
        return configs

    def _read_cache(self) -> Optional[dict]:
        """
        Load the cache file, or None if it is missing, corrupt, or holds
        entries that no longer parse - any of which means "rescan".
        """
        try:
            document = json.loads(_CACHE_FILE.read_text(encoding="utf-8"))
            if document["version"] != _CACHE_VERSION:
                return None
            configs = document["configs"]
            for config in configs.values():
                self._parse_config_json(config)
            return configs
        except (OSError, ValueError, KeyError, TypeError):
            return None

    def _write_cache(self, configs: dict) -> None:
        # Write to a temp file first so the rename is visible atomically
        # rather than as a partially-written file.
        tmp = _CACHE_FILE.with_name(_CACHE_FILE.name + ".tmp")
        tmp.write_text(
            json.dumps(
                {"version": _CACHE_VERSION, "configs": configs},
                indent=2,
                sort_keys=True,
            )
            + "\n",
            encoding="utf-8",
        )
        os.replace(tmp, _CACHE_FILE)

    @staticmethod
    def _parse_config_json(document) -> sDDFDriverConfig:
        resources = document["resources"]
        regions = [
            DTSRegion(
                name=region["name"],
                perms=region.get("perms"),
                size=region.get("size"),
                dt_idx=region.get("dt_index"),
            )
            for region in resources.get("regions", [])
        ]
        irqs = [DTSIRQ(dt_index=irq["dt_index"]) for irq in resources.get("irqs", [])]
        return sDDFDriverConfig(
            compatible=document["compatible"],
            regions=regions,
            irqs=irqs,
        )

    def _materialise(self):
        """
        Rebuild self.map from the cached raw documents plus the current
        subsystem registry.
        """
        new_map: dict[type["sDDFDriverClass"], dict[str, sDDFDriverConfig]] = (
            defaultdict(dict)
        )
        for key, document in self._configs.items():
            # key is "<subsystem>/<driver>", where <driver> may contain slashes.
            subsystem_name, driver_name = key.split("/", 1)
            driver_class = self.subsystems.get(subsystem_name)
            if driver_class is None:
                continue  # not registered yet; materialised at a later rescan
            new_map[driver_class][driver_name] = self._parse_config_json(document)
        self.map = new_map


module_manifest = __sDDFDriverManifest()


def sDDFDriverManifest():
    return module_manifest


def register_sddf_subsystem(subsystem_name: str, driver_class: type["sDDFDriverClass"]):
    """
    Declare the directory name under the drivers tree that holds
    driver_class's drivers, e.g.:

        register_sddf_subsystem("i2c", I2CController)

    The rescan it triggers also materialises anything the tree scan
    found since the cache was last built.
    """
    module_manifest.register_subsystem(subsystem_name, driver_class)
