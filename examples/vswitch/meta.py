# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause
import sys, os
import argparse
import struct
import json
import subprocess
import shutil
from typing import List, Tuple, Callable, Optional
from sdfgen import SystemDescription, Sddf, DeviceTree
from importlib.metadata import version

sys.path.append(
    os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../tools/meta")
)
from board import BOARDS, add_x86_hpet

ProtectionDomain = SystemDescription.ProtectionDomain
MemoryRegion = SystemDescription.MemoryRegion
Map = SystemDescription.Map
Channel = SystemDescription.Channel


# Adds ".elf" to elf strings
def copy_elf(source_elf: str, new_elf: str, elf_number=None):
    source_elf += ".elf"
    if elf_number != None:
        new_elf += str(elf_number)
    new_elf += ".elf"
    assert os.path.isfile(source_elf)
    return shutil.copyfile(source_elf, new_elf)


def generate(
    sdf_file: str,
    output_dir: str,
    dtb: Optional[DeviceTree],
):
    uart_node = None
    ethernet_node = None
    timer_node = None
    if dtb is not None:
        uart_node = dtb.node(board.serial)
        assert uart_node is not None
        ethernet_node = dtb.node(board.ethernet)
        assert ethernet_node is not None
        timer_node = dtb.node(board.timer)
        assert timer_node is not None

    timer_driver = ProtectionDomain("timer_driver", "timer_driver.elf", priority=101)
    timer_system = Sddf.Timer(sdf, timer_node, timer_driver)

    if board.arch == SystemDescription.Arch.X86_64:
        add_x86_hpet(sdf, timer_driver)

    uart_driver = ProtectionDomain("serial_driver", "serial_driver.elf", priority=100)
    serial_virt_tx = ProtectionDomain(
        "serial_virt_tx", "serial_virt_tx.elf", priority=99
    )
    uart_driver = ProtectionDomain(
        "serial_driver",
        "serial_driver.elf",
        priority=100,
    )
    serial_virt_tx = ProtectionDomain(
        "serial_virt_tx",
        "serial_virt_tx.elf",
        priority=99,
    )
    serial_system = Sddf.Serial(sdf, uart_node, uart_driver, serial_virt_tx)

    if board.arch == SystemDescription.Arch.X86_64:
        serial_port = SystemDescription.IoPort(0x3F8, 8, 0)
        uart_driver.add_ioport(serial_port)

    ethernet_driver = ProtectionDomain(
        "ethernet_driver",
        "eth_driver.elf",
        priority=101,
        budget=100,
        period=400,
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

    if board.arch == SystemDescription.Arch.X86_64:
        hw_net_rings = SystemDescription.MemoryRegion(
            sdf, "hw_net_rings", 65536, paddr=0x7A000000
        )
        sdf.add_mr(hw_net_rings)
        hw_net_rings_map = SystemDescription.Map(hw_net_rings, 0x7000_0000, "rw")
        ethernet_driver.add_map(hw_net_rings_map)

        virtio_net_regs = SystemDescription.MemoryRegion(
            sdf, "virtio_net_regs", 0x4000, paddr=0xFE000000
        )
        sdf.add_mr(virtio_net_regs)
        virtio_net_regs_map = SystemDescription.Map(
            virtio_net_regs, 0x6000_0000, "rw", cached=False
        )
        ethernet_driver.add_map(virtio_net_regs_map)

        virtio_net_irq = SystemDescription.IrqIoapic(
            ioapic_id=0, pin=11, vector=1, id=16
        )
        ethernet_driver.add_irq(virtio_net_irq)

        pci_config_address_port = SystemDescription.IoPort(0xCF8, 4, 1)
        ethernet_driver.add_ioport(pci_config_address_port)

        pci_config_data_port = SystemDescription.IoPort(0xCFC, 4, 2)
        ethernet_driver.add_ioport(pci_config_data_port)

    net_virt_tx = ProtectionDomain(
        "net_virt_tx",
        "network_virt_tx.elf",
        priority=100,
        budget=20000,
    )
    net_virt_rx = ProtectionDomain("net_virt_rx", "network_virt_rx.elf", priority=99)

    vswitch = ProtectionDomain("net_vswitch", "network_vswitch.elf", priority=97)

    net_system = Sddf.Net(
        sdf, ethernet_node, ethernet_driver, net_virt_tx, net_virt_rx, vswitch=vswitch
    )

    client0_elf = copy_elf("client", "client", 0)
    client0 = ProtectionDomain("client0", client0_elf, priority=96, budget=20000)
    client0_net_copier = ProtectionDomain(
        "client0_net_copier", "network_copy0.elf", priority=98, budget=20000
    )

    client1_elf = copy_elf("client", "client", 1)
    client1 = ProtectionDomain("client1", client1_elf, priority=96, budget=20000)
    client1_net_copier = ProtectionDomain(
        "client1_net_copier",
        "network_copy1.elf",
        priority=98,
        budget=20000,
    )

    client2_elf = copy_elf("client", "client", 2)
    client2 = ProtectionDomain("client2", client2_elf, priority=96, budget=20000)
    client2_net_copier = ProtectionDomain(
        "client2_net_copier", "network_copy2.elf", priority=98, budget=20000
    )

    client3_elf = copy_elf("client", "client", 3)
    client3 = ProtectionDomain("client3", client3_elf, priority=96, budget=20000)
    client3_net_copier = ProtectionDomain(
        "client3_net_copier", "network_copy3.elf", priority=98, budget=20000
    )

    serial_system.add_client(client0)
    serial_system.add_client(client1)
    serial_system.add_client(client2)
    serial_system.add_client(client3)
    timer_system.add_client(client0)
    timer_system.add_client(client1)
    timer_system.add_client(client2)
    timer_system.add_client(client3)
    net_system.add_client_with_copier(client0, client0_net_copier, vswitch=True)
    net_system.add_client_with_copier(client1, client1_net_copier, vswitch=True)
    net_system.add_client_with_copier(client2, client2_net_copier, vswitch=True)
    net_system.add_client_with_copier(client3, client3_net_copier, vswitch=True)

    client0_lib_sddf_lwip = Sddf.Lwip(sdf, net_system, client0)
    client1_lib_sddf_lwip = Sddf.Lwip(sdf, net_system, client1)
    client2_lib_sddf_lwip = Sddf.Lwip(sdf, net_system, client2)
    client3_lib_sddf_lwip = Sddf.Lwip(sdf, net_system, client3)

    # Echo server protection domains
    pds = [
        uart_driver,
        serial_virt_tx,
        ethernet_driver,
        net_virt_tx,
        net_virt_rx,
        vswitch,
        client0,
        client0_net_copier,
        client1,
        client1_net_copier,
        client2,
        client2_net_copier,
        client3,
        client3_net_copier,
        timer_driver,
    ]
    for pd in pds:
        sdf.add_pd(pd)

    assert serial_system.connect()
    assert serial_system.serialise_config(output_dir)
    assert net_system.connect()

    # ACLs
    # 0 -> 1, 2, 3, V
    # 1 -> 0, 2, V
    # 2 -> 0, 1, V
    # 3 -> 0, V
    net_system.add_acl_rule(client0, client1, True, True)
    net_system.add_acl_rule(client0, client2, True, True)
    net_system.add_acl_rule(client0, client3, True, True)
    net_system.add_acl_rule(client0, net_virt_tx, True, True)
    net_system.add_acl_rule(client1, client2, True, True)
    net_system.add_acl_rule(client1, net_virt_tx, True, True)
    net_system.add_acl_rule(client2, net_virt_tx, True, True)
    net_system.add_acl_rule(client3, net_virt_tx, True, True)

    assert net_system.serialise_config(output_dir)
    assert timer_system.connect()
    assert timer_system.serialise_config(output_dir)
    assert client0_lib_sddf_lwip.connect()
    assert client0_lib_sddf_lwip.serialise_config(output_dir)
    assert client1_lib_sddf_lwip.connect()
    assert client1_lib_sddf_lwip.serialise_config(output_dir)
    assert client2_lib_sddf_lwip.connect()
    assert client2_lib_sddf_lwip.serialise_config(output_dir)
    assert client3_lib_sddf_lwip.connect()
    assert client3_lib_sddf_lwip.serialise_config(output_dir)

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
