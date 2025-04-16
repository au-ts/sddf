#!/usr/bin/env python3
# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause

from pathlib import Path
import unittest

from hardware_backend import *
from runner import runner


async def common(backend: HardwareBackend):
    await wait_for_output(backend, b"Begin input\n")
    await wait_for_output(backend, b"Please give me character!\r\n")
    await wait_for_output(backend, b"Please give me character!\r\n")

    await send_input(backend, b"1234567890")
    await wait_for_output(backend, b"client0 has received 10 characters so far!\r\n")

    # Switch to client 1.
    await send_input(backend, b"\x1c1\r")
    await wait_for_output(backend, b"switching to client 1\r\n")
    await send_input(backend, b"1234567890")
    await wait_for_output(backend, b"client1 has received 10 characters so far!\r\n")


class SerialTests(unittest.IsolatedAsyncioTestCase):
    async def test_odroidc4(self):
        await runner(common, MachineQueueBackend(Path("ci_build/examples/serial/make/odroidc4/debug/loader.img"), "odroidc4_1"))

    async def test_qemu_riscv64(self):
        await runner(
            common,
            QemuBackend(
                "qemu-system-riscv64",
                "-machine",
                "virt",
                "-kernel",
                Path(
                    "ci_build/examples/serial/make/qemu_virt_riscv64/debug/loader.img"
                ).resolve(),
                "-m", "size=2G", "-nographic", "-d", "guest_errors"
            ),
        )


if __name__ == "__main__":
    unittest.main()
