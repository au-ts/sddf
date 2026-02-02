#!/usr/bin/env python3
# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause

import argparse
import os
from pathlib import Path
import sys
import importlib

sys.path.insert(1, Path(__file__).parents[1].as_posix())

from ci.common import TestConfig, backend_fn
from ci.lib.runner import TestFunction, BackendFunction, run_all_examples

EXAMPLES_DIR = Path(__file__).parent / "examples"
EXAMPLES_LIST = sorted(
    [
        e.removesuffix(".py")
        for e in os.listdir(EXAMPLES_DIR)
        if (e.endswith(".py") and e != "__init__.py")
    ]
)

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)

    examples_list = sorted(set(EXAMPLES_LIST))
    if len(examples_list) == 0:
        parser.error("no examples passed")

    matrix: list[TestConfig] = []
    test_fns: dict[str, TestFunction] = {}
    backend_fns: dict[str, BackendFunction] = {}

    for example in examples_list:
        mod = importlib.import_module(f"examples.{example}")
        matrix.extend(mod.TEST_MATRIX)
        test_fns[example.removesuffix(".py")] = mod.test
        custom_backend_fn = callable(getattr(mod, "backend_fn", None))
        if custom_backend_fn:
            backend_fns[example.removesuffix(".py")] = mod.backend_fn
        else:
            backend_fns[example.removesuffix(".py")] = backend_fn

    run_all_examples(examples_list, matrix, test_fns, backend_fns)
