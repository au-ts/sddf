#!/usr/bin/env python3
# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause

from pathlib import Path
from unittest import TestLoader, TestSuite


def load_tests(loader: TestLoader, suite: TestSuite, _pattern: str):
    package_tests = loader.discover(
        start_dir=(Path(__file__).parent / "examples").resolve(), pattern="*.py"
    )

    suite.addTests(package_tests)

    return suite
