#!/usr/bin/env python3
# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause
import os

from .backends import OUTPUT

# For Github Actions etc.
IS_CI = bool(os.environ.get("CI"))


def info(s):
    print("CI|INFO: " + s)


def error(s):
    print("CI|ERROR: " + s)


def group_start(s):
    if IS_CI:
        print(f"::group::{s}")
    else:
        info(s)


def group_end(s):
    info(s)
    if IS_CI:
        print("::endgroup::")
