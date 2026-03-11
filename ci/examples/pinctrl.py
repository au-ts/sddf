#!/usr/bin/env python3
# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause

import asyncio
from pathlib import Path
import sys

sys.path.insert(1, Path(__file__).parents[2].as_posix())

from ci.lib.backends import *
from ci.lib.runner import TestConfig, cli, matrix_product
from ci import common, matrix

TEST_MATRIX = matrix_product(
    board=matrix.EXAMPLES["pinctrl"]["boards_test"],
    config=matrix.EXAMPLES["pinctrl"]["configs"],
    build_system=matrix.EXAMPLES["pinctrl"]["build_systems"],
)


async def test(backend: HardwareBackend, test_config: TestConfig):
    async with asyncio.timeout(10):
        await wait_for_output(backend, b"Begin input\r\n")
        await wait_for_output(backend, b"Please give me character!\r\n")

        await send_input(backend, b"1234567890")
        await expect_output(backend, b"1234567890")
        await wait_for_output(
            backend, b"serial_client has received 10 characters so far!\r\n"
        )


if __name__ == "__main__":
    cli("pinctrl", test, TEST_MATRIX, common.backend_fn, common.loader_img_path)
