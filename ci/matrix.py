#!/usr/bin/env python3
# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause

from __future__ import annotations
from itertools import chain
from typing import TYPE_CHECKING, Any, Literal, Optional, Sequence, TypedDict

from ts_ci import MACHINE_QUEUE_BOARDS, matrix_product
from . import common
from .common import TestConfig, TestFunction, BackendFunction

NO_OUTPUT_DEFAULT_TIMEOUT_S: int = 60


def generate_example_test_cases(
    example: str,
    example_matrix: _ExampleMatrixType,
    test_fn: TestFunction,
    backend_fn: BackendFunction,
    no_output_timeout_s: int,
) -> list[TestConfig]:
    def listify(s: str | Sequence[str]) -> Sequence[str]:
        if isinstance(s, str):
            return [s]
        else:
            return s

    matrix = set(
        matrix_product(
            TestConfig,
            example=[example],
            board=example_matrix["boards"],
            config=example_matrix["configs"],
            build_system=example_matrix["build_systems"],
            test_fn=[test_fn],
            backend_fn=[backend_fn],
            no_output_timeout_s=[no_output_timeout_s],
        )
    )

    for exclude in example_matrix["tests_exclude"]:
        to_exclude = set(
            matrix_product(
                TestConfig,
                example=[example],
                board=listify(exclude.get("board", example_matrix["boards"])),
                config=listify(exclude.get("config", example_matrix["configs"])),
                build_system=listify(
                    exclude.get("build_system", example_matrix["build_systems"])
                ),
                test_fn=[test_fn],
                backend_fn=[backend_fn],
                no_output_timeout_s=[no_output_timeout_s],
            )
        )
        matrix -= to_exclude

    return list(matrix)


EXAMPLES: dict[str, _ExampleMatrixType] = {
    "blk": {
        "configs": ["debug", "release"],
        "build_systems": ["make", "zig"],
        "boards": [
            "maaxboard",
            "qemu_virt_aarch64",
            "qemu_virt_riscv64",
            "x86_64_generic",
        ],
        "tests_exclude": [],
    },
    "i2c": {
        "configs": ["debug", "release"],
        "build_systems": ["make", "zig"],
        "boards": ["odroidc4"],
        "tests_exclude": [],
    },
    # Use i2c bus scan for all devices that don't have an I2C test board
    # attached.
    "i2c_bus_scan": {
        "configs": ["debug", "release"],
        "build_systems": ["make", "zig"],
        "boards": ["serengeti"],
        "tests_exclude": [],
    },
    "echo_server": {
        "configs": ["debug", "release", "benchmark"],
        "build_systems": ["make"],
        "boards": [
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
            "rpi4b_1gb",
            "star64",
            "x86_64_generic",
        ],
        "tests_exclude": [
            # not in machine queue
            {"board": "imx8mp_evk"},
            {"board": "rock3b"},
        ],
    },
    "gpio": {
        "configs": ["debug", "release", "benchmark"],
        "build_systems": ["make"],
        "boards_build": [
            "maaxboard",
        ],
        "boards_test": [],
    },
    "serial": {
        "configs": ["debug", "release"],
        "build_systems": ["make", "zig"],
        "boards": [
            "cheshire",
            "hifive_p550",
            "imx8mm_evk",
            "imx8mq_evk",
            "imx8mp_evk",
            "kria_k26",
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
        "tests_exclude": [
            # not in machine queue
            {"board": "cheshire"},
            {"board": "imx8mp_evk"},
            {"board": "rock3b"},
            {"board": "kria_k26"},
        ],
    },
    "timer": {
        "configs": ["debug", "release"],
        "build_systems": ["make", "zig"],
        "boards": [
            "imx8mq_evk",
            "imx8mp_evk",
            "kria_k26",
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
        "tests_exclude": [
            # does not print anything in release mode, so we don't depend on serial
            {"config": "release"},
            # not in machine queue
            {"board": "imx8mp_evk"},
            {"board": "rock3b"},
            {"board": "kria_k26"},
        ],
    },
}

## Type Hinting + Sanity Checks ##
_BoardNames = Literal[
    "cheshire",
    "hifive_p550",
    "imx8mm_evk",
    "imx8mp_evk",
    "imx8mq_evk",
    "imx8mp_iotgate",
    "kria_k26",
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
    "kria_k26",
}
assert (
    set(_BoardNames.__args__) <= known_board_names  # type: ignore
), f"_BoardNames contains a board that is not valid {known_board_names ^ set(_BoardNames.__args__)}"  # type: ignore

for ex in EXAMPLES.values():
    for board in chain(
        ex["boards"], (excl["board"] for excl in ex["tests_exclude"] if "board" in excl)
    ):
        assert board in known_board_names, f"{board} not a valid board"


class _ExampleMatrixType(TypedDict):
    configs: list[Literal["debug", "release", "benchmark"]]
    build_systems: list[Literal["make", "zig"]]
    boards: list[_BoardNames]
    tests_exclude: list[dict[str, str]]
