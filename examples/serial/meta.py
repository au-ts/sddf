import argparse
from typing import Dict, List, Any
from sdfgen import SystemDescription, Sddf, DeviceTree

ProtectionDomain = SystemDescription.ProtectionDomain

class Board:
    def __init__(self, name: str, arch: SystemDescription.Arch, paddr_top: int, serial_device_node: str):
        self.name = name
        self.arch = arch
        self.paddr_top = paddr_top
        self.serial_device_node = serial_device_node


BOARDS: List[Board] = [
    Board("qemu_virt_aarch64", SystemDescription.Arch.AARCH64, 0xa_000_000, "pl011@9000000"),
    Board("qemu_virt_riscv64", SystemDescription.Arch.RISCV64, 0xa000_0000, "soc/serial@10000000"),
    Board("odroidc4", SystemDescription.Arch.AARCH64, 0x80000000, "soc/bus@ff800000/serial@3000"),
    Board("maaxboard", SystemDescription.Arch.AARCH64, 0xa_000_000, "soc@0/bus@30800000/serial@30860000"),
    Board("imx8mm_evk", SystemDescription.Arch.AARCH64, 0xa_000_000, "soc@0/bus@30800000/spba-bus@30800000/serial@30890000"),
    Board("star64", SystemDescription.Arch.RISCV64, 0x100000000, "soc/serial@10000000"),
]

def generate(sdf_file: str, output_dir: str, dtb: DeviceTree):
    serial_driver = ProtectionDomain("serial_driver", "uart_driver.elf", priority=200)
    serial_virt_tx = ProtectionDomain("serial_virt_tx", "serial_virt_tx.elf", priority=199)
    serial_virt_rx = ProtectionDomain("serial_virt_rx", "serial_virt_rx.elf", priority=199, stack_size=0x2000)
    client0 = ProtectionDomain("client0", "client0.elf", priority=1)
    client1 = ProtectionDomain("client1", "client1.elf", priority=1)

    serial_node = dtb.node(board.serial_device_node)
    assert serial_node is not None

    serial_system = Sddf.Serial(sdf, serial_node, serial_driver, serial_virt_tx, virt_rx=serial_virt_rx)
    serial_system.add_client(client0)
    serial_system.add_client(client1)

    pds = [
        serial_driver,
        serial_virt_tx,
        serial_virt_rx,
        client0,
        client1,
    ]
    for pd in pds:
        sdf.add_pd(pd)

    assert serial_system.connect()
    assert serial_system.serialise_config(output_dir)

    with open(f"{output_dir}/{sdf_file}", "w+") as f:
        f.write(sdf.xml())


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument("--dtb", required=True)
    parser.add_argument("--sddf", required=True)
    parser.add_argument("--board", required=True, choices=[p.name for p in BOARDS])
    parser.add_argument("--output", required=True)
    parser.add_argument("--sdf", required=True)

    args = parser.parse_args()

    board = next(filter(lambda p: p.name == args.board, BOARDS))

    sdf = SystemDescription(board.arch, board.paddr_top)
    sddf = Sddf(args.sddf)

    with open(args.dtb, "rb") as f:
        dtb = DeviceTree(f.read())

    generate(args.sdf, args.output, dtb)
