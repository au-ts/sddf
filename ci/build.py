#!/usr/bin/env python3
# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause

import argparse
import logging
from pathlib import Path
import shutil
import subprocess
import sys
import contextlib

sys.path.insert(1, Path(__file__).parents[1].as_posix())

from ci.lib.runner import TestConfig, matrix_product
from ci import common, matrix

logger = logging.getLogger("CI")


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

    with contextlib.chdir(example_dir):
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
    parser.add_argument("num_jobs", nargs="?", type=int, default=1)
    parser.add_argument("--no-clean", action="store_true")

    args = parser.parse_args()

    if not args.no_clean:
        shutil.rmtree(common.CI_BUILD_DIR)

    for example_name, options in matrix.EXAMPLES.items():
        example_matrix = matrix_product(
            board=options["boards_build"],
            config=options["configs"],
            build_system=options["build_systems"],
        )
        for test_config in example_matrix:
            build(args, example_name, test_config)
