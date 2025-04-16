from io import BytesIO
import sys

from .base import HardwareBackend


async def send_input(
    backend: HardwareBackend, text: bytes, stdout: BytesIO = sys.stdout.buffer
):
    backend.input_stream.write(text)
    stdout.write(text)
    stdout.flush()
    await backend.input_stream.drain()


async def wait_for_output(
    backend: HardwareBackend, text: bytes, stdout: BytesIO = sys.stdout.buffer
) -> bytes:
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
        # we read (at most) the size of text; we may get significantly less
        read = await backend.output_stream.read(len(text))
        stdout.write(read)
        stdout.flush()
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

    chunk = buffer[: index + len(text)]
    return bytes(chunk)
