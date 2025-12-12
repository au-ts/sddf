#!/usr/bin/env python3
# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause

from pathlib import Path
import sys

sys.path.insert(1, Path(__file__).parents[1].as_posix())

from ci.lib.backends import HardwareBackend, QemuBackend, MachineQueueBackend
from ci.lib.runner import TestConfig
from ci.matrix import MACHINE_QUEUE_BOARDS, MACHINE_QUEUE_BOARD_OPTIONS


CI_BUILD_DIR = Path(__file__).parents[1] / "ci_build"


def example_build_path(example_name: str, test_config: TestConfig):
    return (
        CI_BUILD_DIR
        / "examples"
        / example_name
        / test_config.build_system
        / test_config.board
        / test_config.config
    )


def loader_img_path(
    example_name: str,
    test_config: TestConfig,
):
    return (
        example_build_path(example_name, test_config)
        / ("bin" if test_config.build_system == "zig" else "")
        / "loader.img"
    )


def backend_fn(
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
                "-kernel", str(loader_img.resolve()),
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
        elif test_config.board == "x86_64_generic":
            return QemuBackend(
                "qemu-system-x86_64",
                # fmt: off
                "-machine", "q35",
                    # TODO: this is somewhat of a hack
                "-kernel", str(loader_img.parent / "sel4_32.elf"),
                "-initrd", str(loader_img.resolve()),
                "-cpu", "qemu64,+fsgsbase,+pdpe1gb,+pcid,+invpcid,+xsave,+xsaves,+xsaveopt",
                # fmt: on
                *QEMU_COMMON_FLAGS,
            )
        else:
            raise NotImplementedError(f"unknown qemu board {test_config.board}")

    else:
        mq_boards: list[str] = MACHINE_QUEUE_BOARDS[test_config.board]
        options = MACHINE_QUEUE_BOARD_OPTIONS.get(test_config.board, {})
        return MachineQueueBackend(loader_img.resolve(), mq_boards, **options)
