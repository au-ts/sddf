# Copyright 2026, UNSW
# SPDX-License-Identifier: BSD-2-Clause
import argparse
import os
import shutil
import subprocess
import sys
from typing import Optional

from acacia import (
    DeviceTreeBlob,
    Map,
    MemoryRegion,
    ProtectionDomain,
    SchedulingProperties,
    System,
    x86_64,
)
from acacia.irq import IrqIoapic
from acacia.x86 import IOPort

sys.path.append(os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../"))
from acacia_sddf import BOARDS, sDDFEthernet, sDDFLWIP, sDDFSerial, sDDFTimer


# Adds ".elf" to elf strings
def copy_elf(source_elf: str, new_elf: str, elf_number=None):
    source_elf += ".elf"
    if elf_number != None:
        new_elf += str(elf_number)
    new_elf += ".elf"
    assert os.path.isfile(source_elf)
    return shutil.copyfile(source_elf, new_elf)


# Assumes elf string has ".elf" suffix, adds ".data" to data string
def update_elf_section(elf_name: str, section_name: str, data_name: str):
    assert os.path.isfile(elf_name)
    data_name += ".data"
    assert os.path.isfile(data_name)
    assert (
        subprocess.run(
            [
                obj_copy,
                "--update-section",
                "." + section_name + "=" + data_name,
                elf_name,
            ]
        ).returncode
        == 0
    )


def generate(
    sdf_file: str,
    output_dir: str,
):
    timer = sDDFTimer(sdf, board.timer.compatible, board.timer.node_path)
    serial = sDDFSerial(
        sdf,
        board.serial.compatible,
        board.serial.node_path,
        driver_prio=201,
        virt_tx_prio=200,
        allow_rx=False,
        enable_color=True,
        baud_rate=board.baud_rate if board.baud_rate else 115200,
    )

    vswitch = ProtectionDomain(
        sdf,
        "net_vswitch",
        "network_vswitch.elf",
        scheduling=SchedulingProperties(priority=97),
    )
    ethernet = sDDFEthernet(
        sdf,
        board.ethernet.compatible,
        board.ethernet.node_path,
        driver_prio=101,
        virt_tx_prio=100,
        virt_rx_prio=99,
        vswitch=vswitch,
    )

    if board.name == "star64":
        # For ethernet reset, the Pine64 Star64 driver needs access to the
        # clock controller. We do not have a clock driver for this platform so the
        # ethernet driver does it directly.
        clock_controller = MemoryRegion(
            sdf, "clock_controller", 0x10_000, paddr=0x17000000, cached=False
        )
        ethernet.driver.add_map(Map(clock_controller, 0x3000000, "rw"))
    elif board.name == "rpi4b_1gb":
        # Ethernet driver requires timer access to wait for reconfiguration
        timer.add_client(ethernet.driver)

        mbox = MemoryRegion(sdf, "mbox", 0x10_000, paddr=0xFE00B000, cached=False)
        ethernet.driver.add_map(Map(mbox, 0x3000000, "rw"))

    if board.arch == x86_64:
        hw_net_rings = MemoryRegion(
            sdf, "hw_net_rings", 65536, paddr=0x7A000000, cached=False
        )
        ethernet.driver.add_map(Map(hw_net_rings, 0x7000_0000, "rw"))

        virtio_net_regs = MemoryRegion(
            sdf, "virtio_net_regs", 0x4000, paddr=0xFE000000, cached=False
        )
        virtio_net_regs_map = Map(virtio_net_regs, 0x6000_0000, "rw")
        ethernet.driver.add_map(virtio_net_regs_map)

        virtio_net_irq = IrqIoapic(ioapic_id=0, pin=11, vector=1, id=16)
        ethernet.driver.add_irq(virtio_net_irq)

        pci_config_address_port = IOPort(0xCF8, 4, 1)
        ethernet.driver.add_ioport(pci_config_address_port)

        pci_config_data_port = IOPort(0xCFC, 4, 2)
        ethernet.driver.add_ioport(pci_config_data_port)

    client0_elf = copy_elf("client", "client", 0)
    client0 = ProtectionDomain(
        sdf,
        "client0",
        client0_elf,
        scheduling=SchedulingProperties(priority=96, budget=20000),
    )
    client0_net_copier = ProtectionDomain(
        sdf,
        "client0_net_copier",
        "network_copy0.elf",
        scheduling=SchedulingProperties(priority=98, budget=20000),
    )

    client1_elf = copy_elf("client", "client", 1)
    client1 = ProtectionDomain(
        sdf,
        "client1",
        client1_elf,
        scheduling=SchedulingProperties(priority=96, budget=20000),
    )
    client1_net_copier = ProtectionDomain(
        sdf,
        "client1_net_copier",
        "network_copy1.elf",
        scheduling=SchedulingProperties(priority=98, budget=20000),
    )

    client2_elf = copy_elf("client", "client", 2)
    client2 = ProtectionDomain(
        sdf,
        "client2",
        client2_elf,
        scheduling=SchedulingProperties(priority=96, budget=20000),
    )
    client2_net_copier = ProtectionDomain(
        sdf,
        "client2_net_copier",
        "network_copy2.elf",
        scheduling=SchedulingProperties(priority=98, budget=20000),
    )

    client3_elf = copy_elf("client", "client", 3)
    client3 = ProtectionDomain(
        sdf,
        "client3",
        client3_elf,
        scheduling=SchedulingProperties(priority=96, budget=20000),
    )
    client3_net_copier = ProtectionDomain(
        sdf,
        "client3_net_copier",
        "network_copy3.elf",
        scheduling=SchedulingProperties(priority=98, budget=20000),
    )

    serial.add_client(client0)
    serial.add_client(client1)
    serial.add_client(client2)
    serial.add_client(client3)
    timer.add_client(client0)
    timer.add_client(client1)
    timer.add_client(client2)
    timer.add_client(client3)
    ethernet.add_client(client0, copier=client0_net_copier, vswitch_client=True)
    ethernet.add_client(client1, copier=client1_net_copier, vswitch_client=True)
    ethernet.add_client(client2, copier=client2_net_copier, vswitch_client=True)
    ethernet.add_client(client3, copier=client3_net_copier, vswitch_client=True)

    # add LWIPs. Don't need to store subsystem object, it registers with Acacia at init
    sDDFLWIP(ethernet, client0)
    sDDFLWIP(ethernet, client1)
    sDDFLWIP(ethernet, client2)
    sDDFLWIP(ethernet, client3)

    # ACLs
    # 0 -> 1, 2, 3, V
    # 1 -> 0, 2, V
    # 2 -> 0, 1, V
    # 3 -> 0, V
    ethernet.add_acl_rule(client0, client1, True, True)
    ethernet.add_acl_rule(client0, client2, True, True)
    ethernet.add_acl_rule(client0, client3, True, True)
    ethernet.add_acl_rule(client0, ethernet.virt_tx, True, True)
    ethernet.add_acl_rule(client1, client2, True, True)
    ethernet.add_acl_rule(client1, ethernet.virt_tx, True, True)
    ethernet.add_acl_rule(client2, ethernet.virt_tx, True, True)
    ethernet.add_acl_rule(client3, ethernet.virt_tx, True, True)

    sdf.make_config_structs()

    # Patch in timer for rpi4b
    if board.name == "rpi4b_1gb":
        update_elf_section(
            ethernet.driver.prog_image,
            "timer_client_config",
            "eth_driver_timer_client_config",
        )

    sdf.write_xml_file(f"{output_dir}/{sdf_file}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--dtb", required=False)
    parser.add_argument("--sddf", required=True)
    parser.add_argument("--board", required=True, choices=[b.name for b in BOARDS])
    parser.add_argument("--output", required=True)
    parser.add_argument("--sdf", required=True)
    parser.add_argument("--objcopy", required=True)

    args = parser.parse_args()

    board = next(filter(lambda b: b.name == args.board, BOARDS))

    if board.arch != x86_64:
        dtb = DeviceTreeBlob(args.dtb)
    else:
        dtb = None
    sdf = System(board.arch, board.paddr_top, dtb)

    global obj_copy
    obj_copy = args.objcopy

    generate(args.sdf, args.output)
