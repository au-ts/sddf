#!/usr/bin/env python3
# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause

from pathlib import Path
import sys

sys.path.insert(1, Path(__file__).parents[2].as_posix())

from ci.hardware_backend import *
from ci.runner import TestConfig, cli, matrix_product

TEST_MATRIX = matrix_product(
    board=(
        "imx8mm_evk",
        "imx8mq_evk",
        "imx8mp_evk",
        "maaxboard",
        "odroidc2",
        "odroidc4",
        "qemu_virt_aarch64",
        "qemu_virt_riscv64",
        "star64",
    ),
    config=("debug", "release"),
)


async def test(backend: HardwareBackend, test_config: TestConfig):
    await wait_for_output(backend, b"Begin input\n")
    await wait_for_output(backend, b"Please give me character!\r\n")
    await wait_for_output(backend, b"Please give me character!\r\n")

    await send_input(backend, b"1234567890")
    await wait_for_output(backend, b"client0 has received 10 characters so far!\r\n")

    # Switch to client 1.
    await send_input(backend, b"\x1c1\r")
    if test_config.config == "debug":
        await wait_for_output(backend, b"switching to client 1\r\n")
    await send_input(backend, b"1234567890")
    await wait_for_output(backend, b"client1 has received 10 characters so far!\r\n")


if __name__ == "__main__":
    cli("serial", test, TEST_MATRIX)
