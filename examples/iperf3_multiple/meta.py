import sys, os
import argparse
import struct
import json
import subprocess
import shutil
from typing import List, Tuple, Callable
from sdfgen import SystemDescription, Sddf, DeviceTree
from importlib.metadata import version

sys.path.append(
    os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../tools/meta")
)
from board import BOARDS

assert version("sdfgen").split(".")[1] == "28", "Unexpected sdfgen version"

ProtectionDomain = SystemDescription.ProtectionDomain
MemoryRegion = SystemDescription.MemoryRegion
Map = SystemDescription.Map
Channel = SystemDescription.Channel


def copy_elf(source_elf: str, new_elf: str, elf_number=None):
    source_elf += ".elf"
    if elf_number is not None:
        new_elf += str(elf_number)
    new_elf += ".elf"
    assert os.path.isfile(source_elf)
    return shutil.copyfile(source_elf, new_elf)



def generate(
  sdf_file: str, output_dir: str, dtb: DeviceTree, get_core: Callable[[str],int]
):
    uart_node = dtb.node(board.serial)
    assert uart_node is not None
    ethernet_node = dtb.node(board.ethernet)
    assert ethernet_node is not None
    timer_node = dtb.node(board.timer)
    assert timer_node is not None
    
    timer_driver = ProtectionDomain(
        "timer_driver", "timer_driver.elf", priority=101, cpu=get_core("timer_driver")
    )
    timer_system = Sddf.Timer(sdf, timer_node, timer_driver)
    
    uart_driver = ProtectionDomain(
        "serial_driver",
        "serial_driver.elf",
        priority=100,
        cpu=get_core("serial_driver"),
    )
    
    
    
    serial_virt_tx = ProtectionDomain(
        "serial_virt_tx",
        "serial_virt_tx.elf",
        priority=99,
        cpu=get_core("serial_virt_tx"),
    )
    serial_system = Sddf.Serial(sdf, uart_node, uart_driver, serial_virt_tx)
    
    ethernet_driver = ProtectionDomain(
        "ethernet_driver",
        "eth_driver.elf",
        priority=101,
        budget=100,
        period=400,
        cpu=get_core("ethernet_driver"),
    )
    
    if board.name == "star64":
        # For ethernet reset, the Pine64 Star64 driver needs access to the
        # clock controller. We do not have a clock driver for this platform so the
        # ethernet driver does it directly.
        clock_controller = MemoryRegion(
        sdf, "clock_controller", 0x10_000, paddr=0x17000000
        )
        sdf.add_mr(clock_controller)
        ethernet_driver.add_map(Map(clock_controller, 0x3000000, perms="rw"))
    
    net_virt_tx = ProtectionDomain(
        "net_virt_tx",
        "network_virt_tx.elf",
        priority=100,
        budget=20000,
        cpu=get_core("net_virt_tx"),
    )
    
    net_virt_rx = ProtectionDomain(
        "net_virt_rx", "network_virt_rx.elf", priority=99, cpu=get_core("net_virt_rx")
    )
    
    net_system = Sddf.Net(sdf, ethernet_node, ethernet_driver, net_virt_tx, net_virt_rx)
    
    iperf_elf = "iperf3_client.elf"
        # --- make distinct ELF files for each PD instance ---
    iperf_a_elf = copy_elf("iperf3_client", "iperf3_client", 0)
    iperf_b_elf = copy_elf("iperf3_client", "iperf3_client", 1)

    copier_a_elf = copy_elf("network_copy", "network_copy", 0)
    copier_b_elf = copy_elf("network_copy", "network_copy", 1)

    iperf_a = ProtectionDomain(
        "iperf3_a", iperf_a_elf, priority=98, budget=20000, cpu=get_core("iperf3_a")
    )
    iperf_b = ProtectionDomain(
        "iperf3_b", iperf_b_elf, priority=98, budget=20000, cpu=get_core("iperf3_b")
    )

    iperf_net_copier_a = ProtectionDomain(
        "iperf3_net_copier_a", copier_a_elf, priority=97, cpu=get_core("iperf3_net_copier_a")
    )
    iperf_net_copier_b = ProtectionDomain(
        "iperf3_net_copier_b", copier_b_elf, priority=97, cpu=get_core("iperf3_net_copier_b")
    )

    sdf.add_pd(iperf_net_copier_a)
    sdf.add_pd(iperf_net_copier_b)
    sdf.add_pd(iperf_a)
    sdf.add_pd(iperf_b)
    sdf.add_pd(net_virt_rx)
    sdf.add_pd(net_virt_tx)
    sdf.add_pd(ethernet_driver)
    sdf.add_pd(serial_virt_tx)
    sdf.add_pd(timer_driver)
    sdf.add_pd(uart_driver)
    serial_system.add_client(iperf_a)
    serial_system.add_client(iperf_b)
    timer_system.add_client(iperf_a)
    timer_system.add_client(iperf_b)
    
    net_system.add_client_with_copier(iperf_a, iperf_net_copier_a)
    net_system.add_client_with_copier(iperf_b, iperf_net_copier_b)

    lwip_a = Sddf.Lwip(sdf, net_system, iperf_a)
    lwip_b = Sddf.Lwip(sdf, net_system, iperf_b)

    assert serial_system.connect()
    assert serial_system.serialise_config(output_dir)

    assert net_system.connect()
    assert net_system.serialise_config(output_dir)
    
    assert timer_system.connect()
    assert timer_system.serialise_config(output_dir)


    assert lwip_a.connect()
    assert lwip_a.serialise_config(output_dir)

    assert lwip_b.connect()
    assert lwip_b.serialise_config(output_dir)

    with open(f"{output_dir}/{sdf_file}", "w+") as f:
        f.write(sdf.render())
        
if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--dtb", required=True)
    parser.add_argument("--sddf", required=True)
    parser.add_argument("--board", required=True, choices=[b.name for b in BOARDS])
    parser.add_argument("--output", required=True)
    parser.add_argument("--sdf", required=True)
    parser.add_argument("--objcopy", required=True)
    parser.add_argument("--smp", required=True)

    args = parser.parse_args()

    board = next(filter(lambda b: b.name == args.board, BOARDS))

    sdf = SystemDescription(board.arch, board.paddr_top)
    sddf = Sddf(args.sddf)

    global obj_copy
    obj_copy = args.objcopy

    with open(args.smp, "r") as core_alloc:
        core_dict = json.load(core_alloc)
    get_core = lambda name: core_dict[name]

    with open(args.dtb, "rb") as f:
        dtb = DeviceTree(f.read())

    generate(args.sdf, args.output, dtb, get_core)

    
  
 