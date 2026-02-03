#!/usr/bin/env python3
# Copyright 2026, UNSW
# SPDX-License-Identifier: BSD-2-Clause

import asyncio
import sys
from pathlib import Path

sys.path.insert(1, Path(__file__).parents[2].as_posix())

from ci import common, matrix
from ci.lib.backends import *
from ci.lib.runner import TestConfig, cli, matrix_product

TEST_MATRIX = matrix_product(
    board=matrix.EXAMPLES["gpio"]["boards_test"],
    config=matrix.EXAMPLES["gpio"]["configs"],
    build_system=matrix.EXAMPLES["gpio"]["build_systems"],
)


def backend_fn(test_config: TestConfig, loader_img: Path) -> HardwareBackend:
    backend = common.backend_fn(test_config, loader_img)
    return backend


async def test(backend: HardwareBackend, test_config: TestConfig):
    async with asyncio.timeout(60):
        await wait_for_output(backend, b"           	 ... is present!\r\n")


if __name__ == "__main__":
    cli("gpio", test, TEST_MATRIX, backend_fn, common.loader_img_path)
