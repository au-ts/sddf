import os
import sys
import argparse
from dataclasses import dataclass
from typing import List
from sdfgen import SystemDescription, Sddf, DeviceTree
import importlib
from importlib.metadata import version


# WARNING: the system file this generates is incomplete (missing & vaddr-var mapping)
sys.path.append(
    os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../tools/meta")
)

# Use importlib to dynamically load. Using `from` import below other code is bad style.
@dataclass
class Board:
    name: str
    arch: SystemDescription.Arch
    paddr_top: int
    gpio: str
    # The example needs a timer driver to verify the IRQ based loop
    # GPIO itself does not need a timer driver to work
    timer: str


BOARDS: List[Board] = [
    Board(
        name="maaxboard",
        arch=SystemDescription.Arch.AARCH64,
        paddr_top=0x7_0000_000,
        gpio="soc@0/bus@30000000/gpio@30200000",
        timer="soc@0/bus@30000000/timer@302d0000",
    ),
]

# board_module = importlib.import_module("board")

assert version("sdfgen").split(".")[1] == "28", "Unexpected sdfgen version"

ProtectionDomain = SystemDescription.ProtectionDomain

def generate(sdf_file: str, output_dir: str, dtb: DeviceTree):
    timer_node = None
    gpio_node = None

    # Protection domains
    timer_driver = ProtectionDomain("timer", "timer_driver.elf", priority=254, passive=True)
    gpio_driver = ProtectionDomain("gpio_driver", "gpio_driver.elf", priority=254, passive=True)
    telemetry = ProtectionDomain("telemetry", "telemetry.elf", priority=1)
    client = ProtectionDomain("client", "client.elf", priority=1)

    timer_node = dtb.node(board.timer)
    assert timer_node is not None

    gpio_node = dtb.node(board.gpio)
    assert gpio_node is not None

    timer_system = Sddf.Timer(sdf, timer_node, timer_driver)
    timer_system.add_client(client)

    gpio_system = Sddf.Gpio(sdf, gpio_node, gpio_driver)
    driver_channel_ids = [0, 1, 2, 3]
    gpio_system.add_client(client, driver_channel_ids=driver_channel_ids)

    pds = [timer_driver, client, gpio_driver, telemetry]
    for pd in pds:
        sdf.add_pd(pd)

    assert gpio_system.connect()
    assert gpio_system.serialise_config(output_dir)

    assert timer_system.connect()
    assert timer_system.serialise_config(output_dir)

    with open(f"{output_dir}/{sdf_file}", "w+") as f:
        f.write(sdf.render())


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--dtb", required=False)
    parser.add_argument("--sddf", required=True)
    parser.add_argument("--board", required=True, choices=[b.name for b in BOARDS])
    parser.add_argument("--output", required=True)
    parser.add_argument("--sdf", required=True)

    args = parser.parse_args()

    board = next(filter(lambda b: b.name == args.board, BOARDS))

    sdf = SystemDescription(board.arch, board.paddr_top)
    sddf = Sddf(args.sddf)

    dtb = None
    if board.arch != SystemDescription.Arch.X86_64:
        with open(args.dtb, "rb") as f:
            dtb = DeviceTree(f.read())

    generate(args.sdf, args.output, dtb)