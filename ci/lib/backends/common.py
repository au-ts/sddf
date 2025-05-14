#!/usr/bin/env python3
# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause


from contextlib import contextmanager
from dataclasses import dataclass
from pathlib import Path
import sys
from typing import BinaryIO, Union


def reset_terminal():
    OUTPUT.write("\n\x1b[0m")


class TestRetryException(Exception):
    """Test needs to be retried"""


@dataclass
class LockedBoardException(TestRetryException):
    """Board is locked or otherwise unavailable"""

    lock_failures: list[str]

    def __str__(self) -> str:
        out = self.__class__.__name__
        for failure in self.lock_failures:
            out += f"\n - {failure}"
        return out


class TestFailureException(Exception):
    """Test failed"""


class _TeeOut:
    def __init__(self, stdio: BinaryIO):
        self.stdio = stdio
        self.fileio: BinaryIO | None = None

    def write(self, s: Union[bytes, bytearray, str]):
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
