#!/usr/bin/env python3

"""
Runner (CLI) script for running the hardware tests automagically.
This includes automatic, interactive tests using our "Machine Queue" or within
QEMU.
"""

import asyncio
from pathlib import Path
import sys

from hardware_backend import (
    HardwareBackend,
    MachineQueueBackend,
    QemuBackend,
    TtyBackend,
    send_input,
    wait_for_output,
)


async def test1(backend: HardwareBackend):
    await wait_for_output(backend, b"Begin input\n")
    await wait_for_output(backend, b"Please give me character!\r\n")
    await wait_for_output(backend, b"Please give me character!\r\n")

    await send_input(backend, b"1234567890")
    await wait_for_output(backend, b"client0 has received 10 characters so far!\r\n")

    # Switch to client 1.
    await send_input(backend, b"\x1c1\r")
    await wait_for_output(backend, b"switching to client 1\r\n")
    await send_input(backend, b"1234567890")
    await wait_for_output(backend, b"client1 has received 10 characters so far!\r\n")


async def main(backend: str):
    if backend == "qemu":
        backend = QemuBackend("make", "MICROKIT_BOARD=qemu_virt_riscv64", "qemu")
    elif backend == "machine_queue":
        backend = MachineQueueBackend(Path("./build/loader.img"), "odroidc4_1")
    elif backend == "tty":
        backend = TtyBackend("/dev/ttyUSB0")
    else:
        raise Exception("Unknown backend %s" % (backend))

    await backend.start()
    try:
        await test1(backend)
    except asyncio.CancelledError:
        # Reset coloured output.
        print("\x1b[0m\n")
        print("Task cancelled, exiting...", file=sys.stderr)
    except EOFError:
        print("\x1b[0m")
        print("Error: EOF when reading from backend stream", file=sys.stderr)
        quit(1)
    finally:
        await backend.stop()


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--backend", choices=["qemu", "machine_queue", "tty"], required=True
    )
    args = parser.parse_args()

    asyncio.run(main(args.backend))
