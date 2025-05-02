#!/usr/bin/env python3
# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause

import asyncio
from pathlib import Path
import sys

sys.path.insert(1, Path(__file__).parents[2].as_posix())

from ci.lib.backends import *
from ci.lib.runner import TestConfig, cli, matrix_product
from ci.configs import standard_backend, standard_loader_img_path

TEST_MATRIX = matrix_product(
    board=("odroidc4",),
    config=("debug", "release"),
    build_system=("make", "zig"),
)


def backend_fn(test_config: TestConfig, loader_img: Path) -> HardwareBackend:
    backend = standard_backend(test_config, loader_img)

    if isinstance(backend, MachineQueueBackend) and test_config.board == "odroidc4":
        # Only odroidc4_2 is connected to the I²C tests
        backend.board = "odroidc4_2"

    return backend


async def test(backend: HardwareBackend, test_config: TestConfig):
    await wait_for_output(backend, b"DS3231|INFO: init\r\n")

    async with asyncio.timeout(30):
        await wait_for_output(
            backend, b"Set Date and Time on DS3231 to: 31-12-23 23:59:42 (Sunday)\r\n"
        )

        # It should take us less than 20 sec before it becomes Monday.
        await wait_for_output(backend, b"Date and Time: 01-01-24 00:00:00 (Monday)\r\n")


if __name__ == "__main__":
    cli("i2c", test, TEST_MATRIX, backend_fn, standard_loader_img_path)
