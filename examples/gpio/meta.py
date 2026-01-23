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

    # setvar_vaddr="gpio_regs"
    # setvar_vaddr="gpio_ao_regs"

    gpio_driver = ProtectionDomain("gpio_driver", "gpio_driver.elf", priority=100)
    gpio_driver.add_map(SystemDescription.Map(gpio_mr, vaddr=0x4000000, perms="rw", cached=False))
    gpio_driver.add_map(SystemDescription.Map(gpio_ao_mr, vaddr=0x4100000, perms="rw", cached=False))


    client = ProtectionDomain("client", "client.elf", priority=1)
    motor_control_a = ProtectionDomain("motor_control_a", "motor_control_a.elf", priority=2)
    motor_control_b = ProtectionDomain("motor_control_b", "motor_control_b.elf", priority=2)
    ultrasonic_sensor = ProtectionDomain("ultrasonic_sensor", "ultrasonic_sensor.elf", priority=2)

    timer_node = dtb.node(board.timer)
    assert timer_node is not None

    timer_system = Sddf.Timer(sdf, timer_node, timer_driver)
    timer_system.add_client(client)
    timer_system.add_client(motor_control_a)
    timer_system.add_client(motor_control_b)
    timer_system.add_client(ultrasonic_sensor)

    # Client to motors channel
    sdf.add_channel(SystemDescription.Channel(client, motor_control_a, a_id=2, b_id=1, pp_a=True))
    sdf.add_channel(SystemDescription.Channel(client, motor_control_b, a_id=3, b_id=1, pp_a=True))

    # Client to sensor channel
    sdf.add_channel(SystemDescription.Channel(client, ultrasonic_sensor, a_id=4, b_id=1, pp_a=True))

    # Motors to GPIO channel
    sdf.add_channel(SystemDescription.Channel(motor_control_a, gpio_driver, a_id=3, b_id=0, pp_a=True))
    sdf.add_channel(SystemDescription.Channel(motor_control_b, gpio_driver, a_id=3, b_id=1, pp_a=True))

    # Sensors to GPIO channel
    # Echo pin
    sdf.add_channel(SystemDescription.Channel(ultrasonic_sensor, gpio_driver, a_id=3, b_id=2, pp_a=True))

    # Trig pin
    sdf.add_channel(SystemDescription.Channel(ultrasonic_sensor, gpio_driver, a_id=4, b_id=3, pp_a=True))

    pds = [timer_driver, client, motor_control_a, motor_control_b, ultrasonic_sensor, gpio_driver]
    for pd in pds:
        sdf.add_pd(pd)


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