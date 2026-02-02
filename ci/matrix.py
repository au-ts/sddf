#!/usr/bin/env python3
# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause

from __future__ import annotations
from typing import TYPE_CHECKING, Any, Literal, TypedDict

# The ordering in these lists defines an implicit ordering of which boards
# to use for CI preferentially, though all will eventually be tried.
MACHINE_QUEUE_BOARDS: dict[str, list[str]] = {
    "hifive_p550": ["p550a"],
    "serengeti": ["serengeti1", "serengeti2"],
    "imx8mm_evk": ["imx8mm"],
    "imx8mp_iotgate": ["iotgate1"],
    "imx8mq_evk": ["imx8mq", "imx8mq2"],
    "maaxboard": ["maaxboard1", "maaxboard2"],
    "odroidc2": ["odroidc2"],
    "odroidc4": ["odroidc4_1", "odroidc4_2"],
    "star64": ["star64"],
    "zcu102": ["zcu102", "zcu102_2"],
    "rpi4b_1gb": ["pi4B"],
}

MACHINE_QUEUE_BOARD_OPTIONS: dict[str, dict[str, Any]] = {
    "serengeti": dict(uboot_image_started=b"Starting kernel ..."),
    "star64": dict(uboot_image_started=b"Starting kernel ..."),
    "hifive_p550": dict(uboot_image_started=b"Starting kernel ..."),
}

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
            # "x86_64_generic",
            "zcu102",
        ],
    },
}

TEST_TIMEOUTS: dict[str, dict[str, int]] = {"blk": {"qemu_virt_aarch64": 90}}

if TYPE_CHECKING:
    _BoardNames = Literal[
        "odroidc4",
        "imx8mm_evk",
        "imx8mp_evk",
        "imx8mq_evk",
        "maaxboard",
        "odroidc2",
        "serengeti",
        "star64",
        "qemu_virt_aarch64",
        "qemu_virt_riscv64",
        "x86_64_generic",
    ]
    assert set(MACHINE_QUEUE_BOARDS.keys()) == set(_BoardNames.__args__) | {
        "qemu_virt_aarch64",
        "qemu_virt_riscv64",
        "x86_64_generic",
    }

    class _ExampleMatrixType(TypedDict):
        configs: list[Literal["debug", "release", "benchmark"]]
        build_systems: list[Literal["make", "zig"]]
        boards_build: list[_BoardNames]
        boards_test: list[_BoardNames]
