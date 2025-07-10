#!/usr/bin/env python3
# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause


from contextlib import contextmanager
from dataclasses import dataclass
import io
from pathlib import Path
import sys
from typing import BinaryIO, Union


def reset_terminal():
    OUTPUT.write(b"\n\x1b[0m")


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
    def __init__(self, stdout: BinaryIO):
        self.stdout = stdout
        self.fileio: BinaryIO | None = None

    def write(self, s: Union[bytes, bytearray]):
        self.stdout.write(s)
        self.stdout.flush()

        if self.fileio:
            self.fileio.write(s)

    # fmt: off
    def close(self): return self.stdout.close()
    def flush(self): ...
    def readable(self): return False
    def writable(self): return True
    def seekable(self): return False
    @property
    def closed(self): return self.stdout.closed
    # fmt: on


OUTPUT = _TeeOut(sys.stdout.buffer)
sys.stdout = io.TextIOWrapper(OUTPUT, write_through=True)  # type: ignore


@contextmanager
def log_output_to_file(log_file: Path):
    assert OUTPUT.fileio is None

    with open(log_file, mode="wb", buffering=0) as log:
        OUTPUT.fileio = log

        try:
            yield
        finally:
            OUTPUT.fileio = None
