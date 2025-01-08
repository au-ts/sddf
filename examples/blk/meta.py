import argparse
from typing import Dict, List, Any
from sdfgen import SystemDescription, Sddf, DeviceTree

ProtectionDomain = SystemDescription.ProtectionDomain

class Board:
    def __init__(self, name: str, arch: SystemDescription.Arch, paddr_top: int, blk_device_node: str):
        self.name = name
        self.arch = arch
        self.paddr_top = paddr_top
        self.blk_device_node = blk_device_node

# TODO: should be able to derive arch from board?
BOARDS: List[Board] = [
    Board("qemu_virt_aarch64", SystemDescription.Arch.AARCH64, 0x6_0000_000, "virtio_mmio@a003e00"),
    Board("qemu_virt_riscv64", SystemDescription.Arch.RISCV64, 0xa_0000_000, "soc/virtio_mmio@10008000"),
]


def generate_sdf(sdf_file: str, output_dir: str, dtb: DeviceTree):
    blk_driver = ProtectionDomain("blk_driver", "blk_driver.elf", priority=200)
    blk_virt = ProtectionDomain("blk_virt", "blk_virt.elf", priority=199, stack_size=0x2000)
    client = ProtectionDomain("client", "client.elf", priority=1)

    blk_node = dtb.node(board.blk_device_node)
    assert blk_node is not None

    blk_system = Sddf.Block(sdf, blk_node, blk_driver, blk_virt)
    blk_system.add_client(client, partition=0)

    pds = [
        blk_driver,
        blk_virt,
        client
    ]
    for pd in pds:
        sdf.add_pd(pd)

    assert blk_system.connect()
    assert blk_system.serialise_config(output_dir)

    with open(f"{output_dir}/{sdf_file}", "w+") as f:
        f.write(sdf.xml())


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument("--dtb", required=True)
    parser.add_argument("--sddf", required=True)
    parser.add_argument("--board", required=True, choices=[b.name for b in BOARDS])
    parser.add_argument("--output", required=True)
    parser.add_argument("--sdf", required=True)

    args = parser.parse_args()

    board = next(filter(lambda b: b.name == args.board, BOARDS))

    sdf = SystemDescription(board.arch, board.paddr_top)
    sddf = Sddf(args.sddf)

    with open(args.dtb, "rb") as f:
        dtb = DeviceTree(f.read())

    generate_sdf(args.sdf, args.output, dtb)
