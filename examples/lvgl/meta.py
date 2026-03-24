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
Map = SystemDescription.Map
Channel = SystemDescription.Channel
Irq = SystemDescription.IrqConventional

def generate(sdf_file: str, output_dir: str, dtb: DeviceTree):
    timer_node = None
    timer_driver = ProtectionDomain("timer_driver", "timer_driver.elf", priority=253)
    client = ProtectionDomain("client", "client.elf", priority=1, stack_size=0x10000)

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

    fb = MemoryRegion(sdf, "fb", 1024 * 1024 * 8, paddr=0x90000000)
    dma_ctrl = MemoryRegion(sdf, "dma_ctrl", 0x1000, paddr=0xa0000000)
    fw_cfg_mr = MemoryRegion(sdf, "fw-cfg", 0x1000, paddr=0x9020000)
    sdf.add_mr(fw_cfg_mr)
    sdf.add_mr(fb)
    sdf.add_mr(dma_ctrl)
    client.add_map(Map(fw_cfg_mr, 0x9020000, "rw", cached=False))
    client.add_map(Map(fb, 0x90000000, "rw", cached=False))
    client.add_map(Map(dma_ctrl, 0xa0000000, "rw", cached=False))

    ############### virtIO input
    keyboard_driver = ProtectionDomain("virtio_keyboard_driver", "virtio_keyboard_driver.elf", priority=254, stack_size=0x2000)
    mouse_driver = ProtectionDomain("virtio_mouse_driver", "virtio_mouse_driver.elf", priority=254, stack_size=0x2000)

    keyboard_inputs_mr = MemoryRegion(sdf, "keyboard-inputs", size=0x1000)
    mouse_inputs_mr = MemoryRegion(sdf, "mouse-inputs", size=0x1000)
    sdf.add_mr(keyboard_inputs_mr)
    sdf.add_mr(mouse_inputs_mr)

    virtio_mr = MemoryRegion(sdf, "virtio-device", size=0x1000, paddr=0xa003000)
    sdf.add_mr(virtio_mr)

    virtio_keyboard_queues = MemoryRegion(sdf, "virtio-keyboard-queues", size=0x10000, paddr=0x70000000)
    virtio_keyboard_events = MemoryRegion(sdf, "virtio-keyboard-events", size=0x10000, paddr=0x71000000)
    sdf.add_mr(virtio_keyboard_queues)
    sdf.add_mr(virtio_keyboard_events)
    keyboard_driver.add_map(Map(virtio_mr, 0xa003000, perms="rw", cached=False))
    keyboard_driver.add_map(Map(virtio_keyboard_queues, 0x70000000, perms="rw", cached=False))
    keyboard_driver.add_map(Map(virtio_keyboard_events, 0x71000000, perms="rw", cached=False))
    keyboard_driver.add_irq(Irq(irq=79, trigger=Irq.Trigger.EDGE))
    keyboard_driver.add_map(Map(keyboard_inputs_mr, 0x60000000, perms="rw", cached=False))

    virtio_mouse_queues = MemoryRegion(sdf, "virtio-mouse-queues", size=0x10000, paddr=0x80000000)
    virtio_mouse_events = MemoryRegion(sdf, "virtio-mouse-events", size=0x10000, paddr=0x81000000)
    sdf.add_mr(virtio_mouse_queues)
    sdf.add_mr(virtio_mouse_events)
    mouse_driver.add_map(Map(virtio_mr, 0xa003000, perms="rw", cached=False))
    mouse_driver.add_map(Map(virtio_mouse_queues, 0x80000000, perms="rw", cached=False))
    mouse_driver.add_map(Map(virtio_mouse_events, 0x81000000, perms="rw", cached=False))
    mouse_driver.add_irq(Irq(irq=78, trigger=Irq.Trigger.EDGE))
    mouse_driver.add_map(Map(mouse_inputs_mr, 0x60000000, perms="rw", cached=False))

    client.add_map(Map(keyboard_inputs_mr, 0x10000000, perms="rw", cached=False))
    client.add_map(Map(mouse_inputs_mr, 0x20000000, perms="rw", cached=False)) 

    sdf.add_channel(Channel(keyboard_driver, client, a_id=10, b_id=0))
    sdf.add_channel(Channel(mouse_driver, client, a_id=10, b_id=1))
    ###############

    timer_system = Sddf.Timer(sdf, timer_node, timer_driver)
    timer_system.add_client(client)

    pds = [timer_driver, keyboard_driver, mouse_driver, client]
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
