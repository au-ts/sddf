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

# Re-Exports
from .base import HardwareBackend, LockedBoardException
from .streams import send_input, wait_for_output
from .machine_queue import MachineQueueBackend
from .qemu import QemuBackend
from .tty import TtyBackend
