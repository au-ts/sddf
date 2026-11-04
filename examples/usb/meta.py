# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause
import os
import sys
import argparse
from sdfgen import SystemDescription, Sddf, DeviceTree
import importlib
from importlib.metadata import version

sys.path.append(
    os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../tools/meta")
)

# Use importlib to dynamically load. Using `from` import below other code is bad style.
board_module = importlib.import_module("board")
BOARDS = board_module.BOARDS

assert version("sdfgen").split(".")[1] == "28", "Unexpected sdfgen version"

ProtectionDomain = SystemDescription.ProtectionDomain
MemoryRegion = SystemDescription.MemoryRegion
IrqConventional = SystemDescription.IrqConventional
Map = SystemDescription.Map
Channel = SystemDescription.Channel


def generate(sdf_file: str, output_dir: str, dtb: DeviceTree):
    timer_driver = ProtectionDomain("timer_driver", "timer_driver.elf", 253)
    usb_driver = ProtectionDomain("usb_driver", "usb_driver.elf", 252)
    usb_protocol = ProtectionDomain("usb_protocol", "usb_protocol.elf", 251)
    virt_msc = ProtectionDomain("virt_msc", "virt_msc.elf", 240)
    virt_hid = ProtectionDomain("virt_hid", "virt_hid.elf", 240)
    client = ProtectionDomain("client", "client.elf", 200)

    usb_driver.add_irq(IrqConventional(0x49 + 32, id=0))
    driver_to_protocol_channel = Channel(a=usb_driver, b=usb_protocol, a_id=1, b_id=0, pp_b=True)
    
    stack_request_report = Channel(a=virt_hid, b=usb_protocol, a_id=15, b_id=15)
    msc_virt_ppc = Channel(a=virt_msc, b=usb_protocol, a_id=1, b_id=50, pp_a=True)
    msc_virt_mount = Channel(a=virt_msc, b=usb_protocol, a_id=20, b_id=20)
    msc_virt_unmount = Channel(a=virt_msc, b=usb_protocol, a_id=21, b_id=21)
    hid_virt_mount = Channel(a=usb_protocol, b=virt_hid, a_id=31, b_id=31)
    hid_virt_unmount = Channel(a=usb_protocol, b=virt_hid, a_id=32, b_id=32)
    hid_virt_report = Channel(a=usb_protocol, b=virt_hid, a_id=33, b_id=33)
    client_msc_ppc = Channel(a=client, b=virt_msc, a_id=30, b_id=30, pp_a=True)
    client_msc_mount = Channel(a=virt_msc, b=client, a_id=31, b_id=31, notify_b=False)
    client_msc_unmount = Channel(a=virt_msc, b=client, a_id=32, b_id=32, notify_b=False)
    client_hid_mount = Channel(a=virt_hid, b=client, a_id=41, b_id=41, notify_b=False)
    client_hid_unmount = Channel(a=virt_hid, b=client, a_id=42, b_id=42, notify_b=False)
    client_hid_ascii = Channel(a=virt_hid, b=client, a_id=43, b_id=43, notify_b=False)
    client_hid_report = Channel(a=virt_hid, b=client, a_id=44, b_id=44, notify_b=False)

    channels = [
        driver_to_protocol_channel, stack_request_report,
        msc_virt_ppc, msc_virt_mount, msc_virt_unmount,
        hid_virt_mount, hid_virt_unmount, hid_virt_report,
        client_msc_ppc, client_msc_mount, client_msc_unmount,
        client_hid_mount, client_hid_unmount,
        client_hid_ascii, client_hid_report
    ]
    for channel in channels:
        sdf.add_channel(channel)

    # BCM2711 peripherals
    vcmailbox = MemoryRegion(sdf, "vcmailbox", size=0x1000, paddr=0xFE00_B000)
    usb_protocol.add_map(Map(vcmailbox, 0xFE00_B000, "rw", cached=False))

    # DWC2 registers
    regs = MemoryRegion(sdf, name="regs", size=0x10000, paddr=0xFE98_0000)
    usb_driver.add_map(Map(regs, 0xFE98_0000, "rw", cached=False))

    # Regions common to the driver and the protocol stack
    usb_shared = MemoryRegion(sdf, "usb_shared", 0x4000)
    usb_driver.add_map(Map(usb_shared, 0x7000_0000, "rw"))
    usb_protocol.add_map(Map(usb_shared, 0x7000_0000, "rw"))

    # Driver event
    event_queue = MemoryRegion(sdf, "event_queue", 0x1000)
    usb_protocol.add_map(Map(event_queue, 0x7100_0000, "rw"))
    usb_driver.add_map(Map(event_queue, 0x7100_0000, "rw"))

    event_data = MemoryRegion(sdf, "event_data", 0x1000)
    usb_protocol.add_map(Map(event_data, 0x7200_0000, "rw"))
    usb_driver.add_map(Map(event_data, 0x7200_0000, "rw"))

    # Device information
    device_info = MemoryRegion(sdf, "device_info", 0x1000)
    usb_driver.add_map(Map(device_info, 0x7000_4000, "rw"))
    usb_protocol.add_map(Map(device_info, 0x7000_4000, "rw"))
    virt_hid.add_map(Map(device_info, 0x7000_4000, "r"))
    virt_msc.add_map(Map(device_info, 0x7000_4000, "r"))
    client.add_map(Map(device_info, 0x7000_4000, "r"))

    # Protocol-to-HID-virt report
    virt_report_queue = MemoryRegion(sdf, "virt_report_queue", 0x1000)
    usb_protocol.add_map(Map(virt_report_queue, 0x7100_1000, "rw"))
    virt_hid.add_map(Map(virt_report_queue, 0x7100_1000, "rw"))

    virt_report_data = MemoryRegion(sdf, "virt_report_data", 0x1000)
    usb_protocol.add_map(Map(virt_report_data, 0x7200_1000, "rw"))
    virt_hid.add_map(Map(virt_report_data, 0x7200_1000, "rw"))

    # HID-virt-to-client report
    client_report_queue = MemoryRegion(sdf, "client_report_queue", 0x1000)
    virt_hid.add_map(Map(client_report_queue, 0x7100_2000, "rw"))
    client.add_map(Map(client_report_queue, 0x7100_2000, "rw"))

    client_report_data = MemoryRegion(sdf, "client_report_data", 0x1000)
    virt_hid.add_map(Map(client_report_data, 0x7200_2000, "rw"))
    client.add_map(Map(client_report_data, 0x7200_2000, "rw"))

    # HID-virt-to-client ASCII
    client_ascii_queue = MemoryRegion(sdf, "client_ascii_queue", 0x1000)
    virt_hid.add_map(Map(client_ascii_queue, 0x7100_3000, "rw"))
    client.add_map(Map(client_ascii_queue, 0x7100_3000, "rw"))

    client_ascii_data = MemoryRegion(sdf, "client_ascii_data", 0x1000)
    virt_hid.add_map(Map(client_ascii_data, 0x7200_3000, "rw"))
    client.add_map(Map(client_ascii_data, 0x7200_3000, "rw"))

    mrs = [
        vcmailbox, regs,
        usb_shared, device_info,
        event_queue, event_data,
        virt_report_queue, virt_report_data,
        client_report_queue, client_report_data,
        client_ascii_queue, client_ascii_data,
    ]
    for mr in mrs:
        sdf.add_mr(mr)

    timer_node = None
    if board.name == "x86_64_generic":
        # actual interrupt vector = 0 + irq_user_min(0x10) + IRQ_INT_OFFSET(0x20) = 0x30
        hpet_irq = SystemDescription.IrqMsi(0, 0, 0, 0, 0, 0)
        timer_driver.add_irq(hpet_irq)

        hept_regs = SystemDescription.MemoryRegion(
            sdf, "hept_regs", 0x1000, paddr=0xFED00000
        )
        hept_regs_map = SystemDescription.Map(
            hept_regs, 0x5000_0000, "rw", cached=False
        )
        timer_driver.add_map(hept_regs_map)
        sdf.add_mr(hept_regs)
    else:
        timer_node = dtb.node(board.timer)
        assert timer_node is not None

    timer_system = Sddf.Timer(sdf, timer_node, timer_driver)
    timer_system.add_client(usb_protocol)
    timer_system.add_client(virt_hid)

    pds = [timer_driver, usb_driver, usb_protocol, virt_hid, virt_msc, client]
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
