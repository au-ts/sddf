import os
import sys
import argparse
from sdfgen import SystemDescription, Sddf, DeviceTree
import importlib
from importlib.metadata import version


# WARNING: the system file this generates is incomplete (missing & vaddr-var mapping)

sys.path.append(
    os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../tools/meta")
)

# Use importlib to dynamically load. Using `from` import below other code is bad style.
board_module = importlib.import_module("board")
BOARDS = board_module.BOARDS

assert version("sdfgen").split(".")[1] == "28", "Unexpected sdfgen version"

ProtectionDomain = SystemDescription.ProtectionDomain

def generate(sdf_file: str, output_dir: str, dtb: DeviceTree):
    # Memory regions
    gpio_mr = SystemDescription.MemoryRegion(sdf, "gpio", 0x1000,  paddr=0xFF634000)
    gpio_ao_mr = SystemDescription.MemoryRegion(sdf, "gpio_ao", 0x1000,  paddr=0xFF800000)
    sdf.add_mr(gpio_mr)
    sdf.add_mr(gpio_ao_mr)

    # Protection domains
    timer_node = None
    timer_driver = ProtectionDomain("timer", "timer_driver.elf", priority=254)

    telemetry = ProtectionDomain("telemetry", "telemetry.elf", priority=1)

    # setvar_vaddr="gpio_regs"
    # setvar_vaddr="gpio_ao_regs"

    # TODO: make this passive for scheduling
    gpio_driver = ProtectionDomain("gpio_driver", "gpio_driver.elf", priority=100)
    client = ProtectionDomain("client", "client.elf", priority=1)

    timer_node = dtb.node(board.timer)
    assert timer_node is not None

    gpio_node = dtb.node(board.gpio)
    assert gpio_node is not None

    timer_system = Sddf.Timer(sdf, timer_node, timer_driver)
    timer_system.add_client(client)

    gpio_system = Sddf.Gpio(sdf, gpio_node, gpio_driver)
    driver_channel_ids = [3, 4, 5, 6]
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