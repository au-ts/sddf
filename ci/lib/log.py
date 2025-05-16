#!/usr/bin/env python3
# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause
import os

from .backends import OUTPUT

# For Github Actions etc.
IS_CI = bool(os.environ.get("CI"))


def info(s):
    OUTPUT.write("CI|INFO: " + s + "\n")


def error(s):
    OUTPUT.write("CI|ERROR: " + s + "\n")


def group_start(s):
    if IS_CI:
        OUTPUT.write(f"::group::{s}\n")
    else:
        info(s)


def group_end(s):
    info(s)
    if IS_CI:
        OUTPUT.write("::endgroup::\n")
