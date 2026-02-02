#!/usr/bin/env python3
# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause

import asyncio
from pathlib import Path
import sys

sys.path.insert(1, Path(__file__).parents[2].as_posix())

from ci.lib.backends import *
from ci.lib.runner import run_single_example, matrix_product
from ci.common import TestConfig
from ci import common, matrix

TEST_MATRIX = matrix_product(
    example="i2c_bus_scan",
    board=matrix.EXAMPLES["i2c_bus_scan"]["boards_test"],
    config=matrix.EXAMPLES["i2c_bus_scan"]["configs"],
    build_system=matrix.EXAMPLES["i2c_bus_scan"]["build_systems"],
)


def backend_fn(test_config: TestConfig, loader_img: Path) -> HardwareBackend:
    backend = common.backend_fn(test_config, loader_img)
    return backend


async def test(backend: HardwareBackend, test_config: TestConfig):
    async with asyncio.timeout(60):
        await wait_for_output(backend, b"           	 ... is present!\r\n")


if __name__ == "__main__":
    run_single_example(
        "i2c_bus_scan",
        test,
        TEST_MATRIX,
        backend_fn,
    )
