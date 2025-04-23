#!/usr/bin/env python3
# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause

"""
Runner (CLI) script for running the hardware tests automagically.
This includes automatic, interactive tests using our "Machine Queue" or within
QEMU.
"""

import argparse
import asyncio
from collections import deque
from collections.abc import Awaitable, Callable
from dataclasses import dataclass
import itertools
import os
from pathlib import Path
import sys
from typing import Literal

from ci.hardware_backend import HardwareBackend
from ci.hardware_backend.base import LockedBoardException, TestFailureException
from ci.hardware_backend.machine_queue import MachineQueueBackend
from ci.hardware_backend.qemu import QemuBackend


# TODO: Handle timeout / lock failures gracefully (round robin + reasons)
# tftp down prints out: console: Unable to connect to 10.13.1.202:3109


# For Github Actions etc.
IS_CI = bool(os.environ.get("CI"))

LOADER_IMG = "loader.img"


@dataclass(order=True, frozen=True)
class TestConfig:
    board: str
    config: str
    build_system: str = "make"

    def is_qemu(self):
        return self.board.startswith("qemu")


async def runner(
    test: Callable[[HardwareBackend], Awaitable[None]],
    backend: HardwareBackend,
    test_config: TestConfig,
):
    await backend.start()
    try:
        await test(backend, test_config)
    except EOFError:
        raise TestFailureException("EOF when reading from backend stream")
    finally:
        # reset coloured text.
        print("\x1b[0m")
        await backend.stop()


def get_default_backend(
    test_config: TestConfig, ci_build_folder_root: Path
) -> HardwareBackend:

    image = (
        ci_build_folder_root
        / "examples"
        / "serial"
        / test_config.build_system
        / test_config.board
        / test_config.config
        / LOADER_IMG
    )

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
                "-kernel", image.resolve(),
                # fmt: on
                *QEMU_COMMON_FLAGS,
            )
        elif test_config.board == "qemu_virt_aarch64":
            return QemuBackend(
                "qemu-system-aarch64",
                # fmt: off
                "-machine", "virt,virtualization=on",
                "-cpu", "cortex-a53",
                "-device", f"loader,file={image.resolve()},addr=0x70000000,cpu-num=0",
                # fmt: on
                *QEMU_COMMON_FLAGS,
            )
        else:
            raise NotImplementedError(f"unknown qemu board {test_config.board}")

    else:
        MACHINE_QUEUE_MAPPING = {
            "odroidc4": "odroidc4_1",
            "imx8mm_evk": "imx8mm",
            "imx8mp_evk": "iotgate1",
            "imx8mq_evk": "imx8mq",
            "maaxboard": "maaxboard2",
        }
        return MachineQueueBackend(
            image.resolve(),
            MACHINE_QUEUE_MAPPING.get(test_config.board, test_config.board),
        )


def matrix_product(**items):
    assert set(items.keys()) <= set(
        TestConfig.__dataclass_fields__.keys()
    ), "keys subset of config fields"

    return [
        TestConfig(**dict(zip(items.keys(), fields)))
        for fields in itertools.product(*items.values())
    ]


class _ListArg(argparse.Action):
    def __init__(
        self,
        option_strings,
        dest,
        default=None,
    ):
        _option_strings = []
        for option_string in option_strings:
            _option_strings.append(option_string)

            if option_string.startswith("--"):
                option_string = "--exclude-" + option_string[2:]
                _option_strings.append(option_string)

        if not isinstance(default, set):
            raise TypeError(f"default must be a set, got {type(default)}")

        super().__init__(
            option_strings=_option_strings,
            dest=dest,
            default=default,
            # can't use choices as this restricts to single items
            metavar="{" + ",".join(sorted(default)) + "}"
        )

        self.kind: Literal["additive", "subtractive"] | None = None

    def __call__(self, parser, namespace, values, option_string=None):
        values = set(values.split(","))
        if option_string.startswith("--exclude"):
            kind = "subtractive"
            values = self.default - values
        else:
            kind = "additive"

        if self.kind is None:
            self.kind = kind

        if self.kind != kind:
            raise argparse.ArgumentError(
                self,
                "cannot use exclude and non-exclude flags together".format(
                    option_string
                ),
            )

        setattr(namespace, self.dest, values)


def _subset_test_matrix(
    matrix: list[TestConfig], filters: argparse.Namespace
) -> list[TestConfig]:
    def filter_check(test_config):
        implies = lambda a, b: not a or b
        return all(
            [
                (test_config.board in filters.boards),
                (test_config.config in filters.configs),
                (implies(filters.only_qemu, test_config.is_qemu())),
            ]
        )

    return list(filter(filter_check, matrix))


def list_test_cases(matrix: list[TestConfig]):
    if len(matrix) == 0:
        return "   (none)"

    lines = []
    for board, group in itertools.groupby(matrix, key=lambda c: c.board):
        lines.append(
            " - {}: {}".format(
                board, ", ".join(f"{c.config}/{c.build_system}" for c in group)
            )
        )

    return "\n".join(lines)


def clear_colour():
    print("\x1b[0m", end="")


def log_test_start(name: str):
    clear_colour()
    if IS_CI:
        print(f"::group::{name}")
    else:
        print(name)


def log_test_end():
    if IS_CI:
        clear_colour()
        print(f"::endgroup::")

    print()

RESULT_KIND = Literal["pass", "fail", "not_run", "lock_failure", "interrupted"]

def cli(
    test_name: str,
    test: Callable[[HardwareBackend], Awaitable[None]],
    matrix: list[TestConfig],
):
    """
    test should raise an exception on failure.
    matrix is the set of supported test configs for this test.
    """
    parser = argparse.ArgumentParser(description=__doc__)

    filters = parser.add_argument_group(title="filters")
    filters.add_argument(
        "--boards", default={test.board for test in matrix}, action=_ListArg
    )
    filters.add_argument(
        "--configs", default={test.config for test in matrix}, action=_ListArg
    )
    filters.add_argument(
        "--only-qemu", action="store_true", help="select only QEMU tests"
    )

    parser.add_argument(
        "--single",
        action="store_true",
        help="only run the single test selected, failing if the filters applied select more than one test",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="instead of running tests, show what would have been run",
    )
    parser.add_argument(
        "--fast-fail",
        action="store_true",
        help="fail on first test failure",
    )
    parser.add_argument(
        "--override-backend",
        action="store_true",
        help="force the use of a specific backend to run the test. requires --single",
    )

    args = parser.parse_args()

    filters_args = argparse.Namespace(
        **{a.dest: getattr(args, a.dest) for a in filters._group_actions}
    )

    matrix = sorted(_subset_test_matrix(matrix, filters_args))
    if len(matrix) == 0:
        parser.error("applied filters result in zero selected tests")

    if args.override_backend:
        # TODO: Can we tell argparse about this?
        args.single = True
        assert False, "TODO"

    if args.single and len(matrix) != 1:
        parser.error(
            "requested --single but applied filters generated multiple cases: \n"
            + list_test_cases(matrix)
        )

    if args.dry_run:
        print("Would run the following test cases:")
        print(list_test_cases(matrix))
        return


    test_results: dict[TestConfig, RESULT_KIND] = {}
    retry_lock_failures_queue = []

    for test_config in matrix:
        result: RESULT_KIND = "not_run"

        log_test_start(
            f"Running {test_name} on {test_config.board} ({test_config.config}, built with {test_config.build_system})"
        )
        # TODO: override-backend
        backend = get_default_backend(test_config, Path("ci_build"))
        try:
            asyncio.run(runner(test, backend, test_config))
        except TestFailureException as e:
            clear_colour()
            print(e)
            result = "fail"
        except LockedBoardException as e:
            retry_lock_failures_queue.append(test_config)
            clear_colour()
            print(e)
            result = "lock_failure"
        except KeyboardInterrupt:
            clear_colour()
            print("Tests cancelled (SIGINT)")
            result = "interrupted"
        else:
            clear_colour()
            result = "pass"
            print("Test passed")

        log_test_end()
        test_results[test_config] = result

        if result == "interrupted" or (result != "pass" and args.fast_fail):
            break

    passing, failing, lock_failures, not_run = [], [], [], []
    for test_config in matrix:
        result = test_results.get(test_config, "not_run")
        match result:
            case "pass":
                passing.append(test_config)
            case "fail":
                failing.append(test_config)
            case "lock_failure":
                lock_failures.append(test_config)
            case "interrupted" | "not_run":
                not_run.append(test_config)

    print("==== Passing ====")
    print(list_test_cases(passing))
    print("==== Failed =====")
    print(list_test_cases(failing))
    print("===== Cancelled (not run) =====")
    print(list_test_cases(not_run))
    print("===== Failed to acquire locks ====")
    print(list_test_cases(lock_failures))

    if len(passing) != len(matrix):
        quit(1)
