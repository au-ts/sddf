#!/usr/bin/env python3
# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause

"""
Set of "classes" (in the duck-typing way) that describe how we interact with the
actual system that is running the test.

In broad strokes, requirements of these backends are:

- Can collect log outputs (at a line granularity, i.e. streaming)
- Can enter test inputs
- Can kill tests.
"""

# Setup asyncio.timeout, contextlib.chdir
from . import polyfills

# Re-Exports
from .base import HardwareBackend
from .common import (
    LockedBoardException,
    TestFailureException,
    TestRetryException,
    reset_terminal,
    log_output_to_file,
    OUTPUT,
    TeeOut,
)
from .streams import send_input, wait_for_output, expect_output
from .machine_queue import MachineQueueBackend
from .qemu import QemuBackend
from .tty import TtyBackend

__all__ = (
    # .base
    "HardwareBackend",
    # .common
    "LockedBoardException",
    "TestFailureException",
    "TestRetryException",
    "reset_terminal",
    "log_output_to_file",
    "OUTPUT",
    "TeeOut",
    # .streams
    "send_input",
    "wait_for_output",
    "expect_output",
    # backends
    "MachineQueueBackend",
    "QemuBackend",
    "TtyBackend",
)
