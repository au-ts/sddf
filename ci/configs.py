#!/usr/bin/env python3
# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause

from pathlib import Path

from ci.lib.backends import HardwareBackend, QemuBackend, MachineQueueBackend
from ci.lib.runner import TestConfig


MACHINE_QUEUE_MAPPING = {
    "odroidc4": "odroidc4_1",
    "imx8mm_evk": "imx8mm",
    "imx8mp_evk": "iotgate1",
    "imx8mq_evk": "imx8mq",
    "maaxboard": "maaxboard2",
}


def standard_loader_img_path(
    example_name: str,
    test_config: TestConfig,
):
    return (
        Path(__file__).parents[1]
        / "ci_build"
        / "examples"
        / example_name
        / test_config.build_system
        / test_config.board
        / test_config.config
        / ("bin" if test_config.build_system == "zig" else "")
        / "loader.img"
    )


def standard_backend(
    test_config: TestConfig,
    loader_img: Path,
) -> HardwareBackend:

    if test_config.is_qemu():
        QEMU_COMMON_FLAGS = (
            # fmt: off
            "-m", "size=2G",
            "-serial", "mon:stdio",
            "-nographic",
            "-d", "guest_errors",
            # fmt: on
        )

        if test_config.board == "qemu_virt_riscv64":
            return QemuBackend(
                "qemu-system-riscv64",
                # fmt: off
                "-machine", "virt",
                "-kernel", loader_img.resolve(),
                # fmt: on
                *QEMU_COMMON_FLAGS,
            )
        elif test_config.board == "qemu_virt_aarch64":
            return QemuBackend(
                "qemu-system-aarch64",
                # fmt: off
                "-machine", "virt,virtualization=on",
                "-cpu", "cortex-a53",
                "-device", f"loader,file={loader_img.resolve()},addr=0x70000000,cpu-num=0",
                # fmt: on
                *QEMU_COMMON_FLAGS,
            )
        else:
            raise NotImplementedError(f"unknown qemu board {test_config.board}")

    else:
        return MachineQueueBackend(
            loader_img.resolve(),
            MACHINE_QUEUE_MAPPING.get(test_config.board, test_config.board),
        )
