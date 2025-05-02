#!/usr/bin/env python3
# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause


from contextlib import contextmanager
from pathlib import Path
import sys
from typing import BinaryIO


def reset_terminal():
    print("\n\x1b[0m", end="")


class LockedBoardException(Exception):
    """Board is locked and we were told not to poll."""


class TestFailureException(Exception):
    """Test failed"""


class _TeeOut:
    def __init__(self, stdio: BinaryIO):
        self.stdio = stdio
        self.fileio: BinaryIO | None = None

    def write(self, s: bytes | bytearray | str):
        if isinstance(s, str):
            s = s.encode()

        self.stdio.write(s)
        self.stdio.flush()

        if self.fileio:
            self.fileio.write(s)


OUTPUT = _TeeOut(sys.stdout.buffer)


@contextmanager
def log_output_to_file(log_file: Path):
    assert OUTPUT.fileio is None

    with open(log_file, mode="wb", buffering=0) as log:
        OUTPUT.fileio = log

        try:
            yield
        finally:
            OUTPUT.fileio = None
