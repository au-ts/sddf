#!/usr/bin/env python3
# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause

from __future__ import annotations
from itertools import chain
from typing import TYPE_CHECKING, Any, Literal, TypedDict

from ts_ci import MACHINE_QUEUE_BOARDS

NO_OUTPUT_DEFAULT_TIMEOUT_S: int = 60

EXAMPLES: dict[str, _ExampleMatrixType] = {
    "blk": {
        "configs": ["debug", "release"],
        "build_systems": ["make", "zig"],
        "boards_build": [
            "maaxboard",
            "qemu_virt_aarch64",
            "qemu_virt_riscv64",
            "x86_64_generic",
        ],
        "boards_test": [
            "maaxboard",
            "qemu_virt_aarch64",
            "qemu_virt_riscv64",
            "x86_64_generic",
        ],
    },
    "i2c": {
        "configs": ["debug", "release"],
        "build_systems": ["make", "zig"],
        "boards_build": ["odroidc4"],
        "boards_test": ["odroidc4"],
    },
    # Use i2c bus scan for all devices that don't have an I2C test board
    # attached.
    "i2c_bus_scan": {
        "configs": ["debug", "release"],
        "build_systems": ["make", "zig"],
        "boards_build": ["serengeti"],
        "boards_test": ["serengeti"],
    },
    "echo_server": {
        "configs": ["debug", "release", "benchmark"],
        "build_systems": ["make"],
        "boards_build": [
            "imx8mm_evk",
            "imx8mq_evk",
            "imx8mp_evk",
            "imx8mp_iotgate",
            "maaxboard",
            "odroidc2",
            "odroidc4",
            "qemu_virt_aarch64",
            "qemu_virt_riscv64",
            "rock3b",
            "star64",
            "x86_64_generic",
        ],
        "boards_test": [
            "imx8mm_evk",
            "imx8mq_evk",
            "imx8mp_iotgate",
            "maaxboard",
            "odroidc2",
            "odroidc4",
            "qemu_virt_aarch64",
            "qemu_virt_riscv64",
            "star64",
        ],
    },
    "serial": {
        "configs": ["debug", "release"],
        "build_systems": ["make", "zig"],
        "boards_build": [
            "cheshire",
            "hifive_p550",
            "imx8mm_evk",
            "imx8mq_evk",
            "imx8mp_evk",
            "maaxboard",
            "odroidc2",
            "odroidc4",
            "qemu_virt_aarch64",
            "qemu_virt_riscv64",
            "rock3b",
            "rpi4b_1gb",
            "serengeti",
            "star64",
            "x86_64_generic",
            "zcu102",
        ],
        "boards_test": [
            "hifive_p550",
            "imx8mm_evk",
            "imx8mq_evk",
            "maaxboard",
            "odroidc2",
            "odroidc4",
            "qemu_virt_aarch64",
            "qemu_virt_riscv64",
            "rpi4b_1gb",
            "serengeti",
            "star64",
            "x86_64_generic",
            "zcu102",
        ],
    },
    "timer": {
        # Only works in debug mode so as to not depend on serial
        "configs": ["debug"],
        "build_systems": ["make", "zig"],
        # TODO:
        # "tests_exclude": [
        #     { "config": "release "},
        #     { "config", "debug", "build": "zig", board: "odroid"}
        # ],
        "boards_build": [
            "imx8mq_evk",
            "imx8mp_evk",
            "maaxboard",
            "odroidc2",
            "odroidc4",
            "qemu_virt_aarch64",
            "qemu_virt_riscv64",
            "rock3b",
            "rpi4b_1gb",
            "star64",
            "serengeti",
            "x86_64_generic",
            "zcu102",
        ],
        "boards_test": [
            "imx8mq_evk",
            "maaxboard",
            "odroidc2",
            "odroidc4",
            "qemu_virt_aarch64",
            "qemu_virt_riscv64",
            "rpi4b_1gb",
            "serengeti",
            "star64",
            "x86_64_generic",
            "zcu102",
        ],
    },
}

## Type Hinting + Sanity Checks ##
_BoardNames = Literal[
    "cheshire",
    "odroidc4",
    "imx8mm_evk",
    "imx8mp_evk",
    "imx8mq_evk",
    "imx8mp_iotgate",
    "hifive_p550",
    "maaxboard",
    "odroidc2",
    "odroidc4",
    "rpi4b_1gb",
    "rock3b",
    "serengeti",
    "star64",
    "qemu_virt_aarch64",
    "qemu_virt_riscv64",
    "x86_64_generic",
    "zcu102",
]

known_board_names = set(MACHINE_QUEUE_BOARDS.keys()) | {
    # simulation boards
    "qemu_virt_aarch64",
    "qemu_virt_riscv64",
    "x86_64_generic",
    # build only
    "imx8mp_evk",
    "rock3b",
    "cheshire",
}
assert (
    set(_BoardNames.__args__) <= known_board_names
), f"_BoardNames contains a board that is not valid {known_board_names ^ set(_BoardNames.__args__)}"

for ex in EXAMPLES.values():
    for board in chain(ex["boards_build"], ex["boards_test"]):
        assert board in known_board_names, f"{board} not a valid board"


class _ExampleMatrixType(TypedDict):
    configs: list[Literal["debug", "release", "benchmark"]]
    build_systems: list[Literal["make", "zig"]]
    boards_build: list[_BoardNames]
    boards_test: list[_BoardNames]
