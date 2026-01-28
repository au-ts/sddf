#!/usr/bin/env python3
# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause

import asyncio
import inspect
from functools import wraps

from .. import log
from .base import HardwareBackend
from .common import OUTPUT, reset_terminal, TestFailureException


def _print_text_on_timeout(f):
    @wraps(f)
    async def wrapper(*args, **kwargs):
        text = inspect.getcallargs(f, *args, **kwargs)["text"]
        try:
            return await f(*args, **kwargs)
        except asyncio.CancelledError:
            reset_terminal()
            log.info(
                "'{}' was cancelled/timed out whilst waiting for {}".format(
                    f.__name__, text
                )
            )
            raise

    return wrapper


async def send_input(backend: HardwareBackend, text: bytes):
    backend.input_stream.write(text)
    OUTPUT.write(text)
    await backend.input_stream.drain()


@_print_text_on_timeout
async def wait_for_output(backend: HardwareBackend, text: bytes) -> bytes:
    if len(text) == 0:
        raise ValueError("Text should be at least 1 byte")

    buffer = bytearray()

    # This is basically the implementation of StreamReader.readuntil.
    # Some comments are taken verbatim from Lib/asyncio/streams.py
    # Licensed under Zero-Clause BSD https://docs.python.org/3/license.html#bsd0.
    # We can't use it, because we want to log continuously.

    # `offset` is the number of bytes from the beginning of the buffer
    # where there is no occurrence of `text`.
    offset = 0

    # Loop until we find `text` in the buffer, exceed the buffer size,
    # or an EOF has happened.
    while True:
        # we read a single character; if we read more than that, then we run
        # the risk of consuming more input than we desired, and thus missing
        # part of the output next time.
        # TODO: backwards seek?
        read = await backend.output_stream.read(1)
        if read == b"":
            raise EOFError()

        OUTPUT.write(read)
        buffer.extend(read)

        # Check if we now have enough data in the buffer for `text` to fit.
        if len(buffer) - offset >= len(text):
            index = buffer.find(text, offset)
            if index != -1:
                # `text` is in the buffer
                break

            # We can start ignoring text that was before len(text) since
            # we can't find a match with text more than that far from the end.
            offset = len(buffer) + 1 - len(text)

    if b"LDR|ERROR: loader trapped exception: Synchronous" in buffer:
        raise TestFailureException(
            "loader trapped. Backtrace avialable."
            )

    return buffer


@_print_text_on_timeout
async def expect_output(backend: HardwareBackend, text: bytes):
    if len(text) == 0:
        raise ValueError("Text should be at least 1 byte")

    read = await backend.output_stream.readexactly(len(text))
    OUTPUT.write(read)

    if text not in read:
        raise TestFailureException(
            "failed to find expected {} in stream; did receive {}".format(text, read)
        )
