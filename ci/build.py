#!/usr/bin/env python3
# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause

import argparse
import logging
import os
from pathlib import Path
import shutil
import subprocess
import sys
import contextlib

sys.path.insert(1, Path(__file__).parents[1].as_posix())

from ci.lib.runner import ArgparseActionList, TestConfig, matrix_product
from ci import common, matrix

logger = logging.getLogger("CI")


# python 3.11 backport
@contextlib.contextmanager
def chdir(path):
    old_cwd = os.getcwd()
    os.chdir(path)
    try:
        yield
    finally:
        os.chdir(old_cwd)


def get_example_dir(example_name: str):
    SDDF = Path(__file__).parents[1]
    return SDDF / "examples" / example_name


def build_make(args: argparse.Namespace, example_name: str, test_config: TestConfig):
    build_dir = common.example_build_path(example_name, test_config)
    example_dir = get_example_dir(example_name)

    subprocess.run(
        [
            "make",
            f"--jobs={args.num_jobs}",
            f"--directory={example_dir}",
            f"BUILD_DIR={build_dir}",
            f"MICROKIT_SDK={args.microkit_sdk}",
            f"MICROKIT_BOARD={test_config.board}",
            f"MICROKIT_CONFIG={test_config.config}",
        ],
        check=True,
    )


def build_zig(args: argparse.Namespace, example_name: str, test_config: TestConfig):
    build_dir = common.example_build_path(example_name, test_config)
    example_dir = get_example_dir(example_name)

    zig_env = os.environ.copy()
    zig_env["ZIG_GLOBAL_CACHE_DIR"] = str(common.CI_BUILD_DIR / "zig-cache")
    zig_env["ZIG_LOCAL_CACHE_DIR"] = str(build_dir / "zig-cache")

    with chdir(example_dir):
        subprocess.run(
            [
                "zig",
                "build",
                f"-Dsdk={args.microkit_sdk}",
                f"-Dboard={test_config.board}",
                f"-Dconfig={test_config.config}",
                "-p",
                build_dir,
            ],
            check=True,
            env=zig_env,
        )


def build(args: argparse.Namespace, example_name: str, test_config: TestConfig):
    logger.info(
        "building example '%s' for '%s' with microkit config '%s' and '%s'"
        % (
            example_name,
            test_config.board,
            test_config.config,
            test_config.build_system,
        )
    )

    if test_config.build_system == "make":
        build_make(args, example_name, test_config)
    elif test_config.build_system == "zig":
        build_zig(args, example_name, test_config)
    else:
        raise NotImplementedError(f"unknown build system '{test_config.build_system}'")


if __name__ == "__main__":
    logging.basicConfig(level=logging.INFO)
    parser = argparse.ArgumentParser(description=__doc__)

    parser.add_argument("microkit_sdk")
    parser.add_argument(
        # len(os.sched_getaffinity(0)) matches behaviour of $(nproc)
        "num_jobs", nargs="?", type=int, default=len(os.sched_getaffinity(0))
    )
    parser.add_argument(
        "--examples",
        default=set(matrix.EXAMPLES.keys()),
        action=ArgparseActionList,
    )
    parser.add_argument("--no-clean", action="store_true")

    args = parser.parse_args()

    if not args.no_clean:
        try:
            shutil.rmtree(common.CI_BUILD_DIR)
        except FileNotFoundError:
            pass

    for example_name, options in matrix.EXAMPLES.items():
        if example_name not in args.examples:
            continue

        example_matrix = matrix_product(
            board=options["boards_build"],
            config=options["configs"],
            build_system=options["build_systems"],
        )
        for test_config in example_matrix:
            build(args, example_name, test_config)
