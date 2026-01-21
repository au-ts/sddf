#!/usr/bin/env python3
# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause

import asyncio
import functools
import subprocess
from pathlib import Path
import sys
import tempfile

sys.path.insert(1, Path(__file__).parents[2].as_posix())

from ci.lib.backends import *
from ci.lib.runner import TestConfig, cli, matrix_product
from ci import common, matrix

TEST_MATRIX = matrix_product(
    board=matrix.EXAMPLES["blk"]["boards_test"],
    config=matrix.EXAMPLES["blk"]["configs"],
    build_system=matrix.EXAMPLES["blk"]["build_systems"],
)

SDDF = Path(__file__).parents[2]
mkvirtdisk = (SDDF / "tools" / "mkvirtdisk").resolve()


def backend_fn(
    disks_dir: str, test_config: TestConfig, loader_img: Path
) -> HardwareBackend:
    backend = common.backend_fn(test_config, loader_img)

    if isinstance(backend, QemuBackend):
        (_, disk_path) = tempfile.mkstemp(dir=disks_dir)

        subprocess.run(
            [mkvirtdisk, disk_path, "1", "512", "16777216", "GPT"],
            check=True,
            capture_output=True,
        )

        # fmt: off
        backend.invocation_args.extend([
            "-global", "virtio-mmio.force-legacy=false",
            "-drive", "file={},if=none,format=raw,id=hd".format(disk_path),
            "-device", "virtio-blk-pci,drive=hd" if test_config.board == "x86_64_generic" else "virtio-blk-device,drive=hd",
        ])
        # fmt: on

    return backend


async def test(backend: HardwareBackend, test_config: TestConfig):
    async with asyncio.timeout(10):
        await wait_for_output(backend, b"CLIENT|INFO: starting\r\n")
    async with asyncio.timeout(10):
        await wait_for_output(backend, b"device config ready\r\n")
        await wait_for_output(backend, b"basic: STATE_CHECK_READ state\r\n")
        await wait_for_output(
            backend, b"CLIENT|INFO: basic: successfully finished!\r\n"
        )


if __name__ == "__main__":
    with tempfile.TemporaryDirectory(suffix="sddf_blk_disks") as qemu_disks_dir:
        cli(
            "blk",
            test,
            TEST_MATRIX,
            functools.partial(backend_fn, qemu_disks_dir),
            common.loader_img_path,
        )
