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

from board import BOARDS

# # Use importlib to dynamically load. Using `from` import below other code is bad style.
# @dataclass
# class Board:
#     name: str
#     arch: SystemDescription.Arch
#     paddr_top: int
#     gpio: str
#     # The example needs a timer driver to verify the IRQ based loop
#     # GPIO itself does not need a timer driver to work
#     timer: str


# BOARDS: List[Board] = [
#     Board(
#         name="maaxboard",
#         arch=SystemDescription.Arch.AARCH64,
#         paddr_top=0x7_0000_000,
#         # Use GPIO bank 3 - gpio2 in dts
#         gpio="soc@0/bus@30000000/gpio@30220000",
#         timer="soc@0/bus@30000000/timer@302d0000",
#     ),
# ]

# board_module = importlib.import_module("board")

assert version("sdfgen").split(".")[1] == "29", "Unexpected sdfgen version"

ProtectionDomain = SystemDescription.ProtectionDomain

def generate(sdf_file: str, output_dir: str, dtb: DeviceTree):
    timer_node = None
    gpio_node = None
    serial_node = None

    # Protection domains
    serial_driver = ProtectionDomain("serial_driver", "serial_driver.elf", priority=200)
    # Increase the stack size as running with UBSAN uses more stack space than normal.
    serial_virt_tx = ProtectionDomain(
        "serial_virt_tx", "serial_virt_tx.elf", priority=199, stack_size=0x2000
    )
    clk_driver = ProtectionDomain("clk_driver", "clk_driver.elf", priority=150, passive=True)
    # Ensure the priority is exclusively the highest as the pinctrl driver must run first!
    # This is enforced by sdfgen at the render() step.
    pinctrl_driver = ProtectionDomain(
        "pinctrl_driver", "pinctrl_driver.elf", priority=253
    )
    pinctrl_node = dtb.node(board.pinctrl)
    assert pinctrl_node is not None
    pinctrl_system = Sddf.Pinctrl(sdf, pinctrl_node, pinctrl_driver)

    pwm_driver = ProtectionDomain("pwm_driver", "pwm_driver.elf", priority=100)

    timer_driver = ProtectionDomain("timer", "timer_driver.elf", priority=254, passive=True)
    gpio_driver = ProtectionDomain("gpio_driver", "gpio_driver.elf", priority=254, passive=True)
    # telemetry = ProtectionDomain("telemetry", "telemetry.elf", priority=1, budget=2000, period=8000)
    # client = ProtectionDomain("client", "client.elf", priority=2, budget=1500000, period=2000000)
    client = ProtectionDomain("client", "client.elf", priority=2)

    serial_node = dtb.node(board.serial)
    assert serial_node is not None

    timer_node = dtb.node(board.timer)
    assert timer_node is not None

    gpio_node = dtb.node(board.gpio)
    assert gpio_node is not None

    if board.name != "maaxboard":
        assert False
    
    # HACK for sdfgen.             "soc@0/bus@30400000/pwm@30670000",
    pwm1_mr = MemoryRegion(sdf, "pwm1", 0x10_000, paddr=0x30660000)
    pwm2_mr = MemoryRegion(sdf, "pwm2", 0x10_000, paddr=0x30670000)
    pwm3_mr = MemoryRegion(sdf, "pwm3", 0x10_000, paddr=0x30680000)
    pwm4_mr = MemoryRegion(sdf, "pwm4", 0x10_000, paddr=0x30690000)
    sdf.add_mr(pwm1_mr)
    sdf.add_mr(pwm2_mr)
    sdf.add_mr(pwm3_mr)
    sdf.add_mr(pwm4_mr)
    pwm_driver.add_map(Map(pwm1_mr, 0x30_000_000, "rw", cached=False))
    pwm_driver.add_map(Map(pwm2_mr, 0x30_010_000, "rw", cached=False))
    pwm_driver.add_map(Map(pwm3_mr, 0x30_020_000, "rw", cached=False))
    pwm_driver.add_map(Map(pwm4_mr, 0x30_030_000, "rw", cached=False))

    # HACK: sdfgen doesn't support multiple regions for a device resource yet
    #       or the clk class. This will be removed in the pending sdfgen refactor.
    #       We can add direct support for the Maaxboard via boards.py, but
    #       the odroid clk driver depends on numerous maps that aren't in the DTS
    #       at all, meaning this switch is the best we can do for now.
    if board.name == "maaxboard":
        clk_ccm_mr = MemoryRegion(sdf, "clk_ccm", 0xd000, paddr=0x30380000)
        clk_ccm_analog_mr = MemoryRegion(sdf, "clk_ccm_analog", 0x1000, paddr=0x30360000)
        sdf.add_mr(clk_ccm_mr)
        sdf.add_mr(clk_ccm_analog_mr)

        clk_ccm_map = Map(clk_ccm_mr, 0x3200000, "rw", cached=False)
        clk_ccm_analog_map = Map(clk_ccm_analog_mr, 0x3300000, "rw", cached=False)
        clk_driver.add_map(clk_ccm_map)
        clk_driver.add_map(clk_ccm_analog_map)
    else:
        print("Unsupported board!")
        exit(-1)

    clk_channel = Channel(clk_driver, pwm_driver, pp_b=True)
    sdf.add_channel(clk_channel)
    assert clk_channel.pd_b_id == 0, clk_channel.pd_b_id


    timer_system = Sddf.Timer(sdf, timer_node, timer_driver)
    timer_system.add_client(client)

    gpio_system = Sddf.Gpio(sdf, gpio_node, gpio_driver)
    driver_channel_ids = [0, 1, 2, 3, 4, 5, 6, 7]
    gpio_system.add_client(client, driver_channel_ids=driver_channel_ids)

    # clients
    chan = Channel(pwm_driver, client, pp_b=True, notify_a=False, notify_b=False)
    sdf.add_channel(chan)
    assert chan.pd_a_id == 1, chan.pd_a_id
    assert chan.pd_b_id == 0, chan.pd_b_id

    serial_system = Sddf.Serial(sdf, serial_node, serial_driver, serial_virt_tx)
    serial_system.add_client(client)

    pds = [
        timer_driver, 
        client, 
        gpio_driver,
        serial_driver,
        serial_virt_tx,
        pinctrl_driver,
        clk_driver,
        pwm_driver
    ]

    for pd in pds:
        sdf.add_pd(pd)

    assert serial_system.connect()
    assert serial_system.serialise_config(output_dir)

    assert pinctrl_system.connect()
    assert pinctrl_system.serialise_config(output_dir)

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