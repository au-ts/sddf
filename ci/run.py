#!/usr/bin/env python3
# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause

import importlib
import os
from pathlib import Path
import sys

from ts_ci import log, TestConfig, TestMetadata, run_tests

sys.path.insert(1, Path(__file__).parents[1].as_posix())

EXAMPLES_DIR = Path(__file__).parent / "examples"
EXAMPLES_LIST = sorted(
    [
        e.removesuffix(".py")
        for e in os.listdir(EXAMPLES_DIR)
        if (e.endswith(".py") and e != "__init__.py")
    ]
)

if __name__ == "__main__":
    examples_list = sorted(set(EXAMPLES_LIST))
    if len(examples_list) == 0:
        log.error("no examples found")
        exit(1)

    matrix: list[TestConfig] = []
    test_metadatas: dict[str, TestMetadata] = {}

    for example in examples_list:
        mod = importlib.import_module(f"ci.examples.{example}")
        matrix.extend(mod.TEST_MATRIX)
        test_metadatas[example] = mod.TEST_METADATA

    run_tests(test_metadatas, matrix)
