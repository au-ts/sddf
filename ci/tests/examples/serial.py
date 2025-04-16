from ...hardware_backend import HardwareBackend, wait_for_output, send_input
from ...runner import cli


async def test(backend: HardwareBackend):
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


if __name__ == "__main__":
    cli(test)
