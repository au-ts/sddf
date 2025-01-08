import argparse
from typing import Dict, List, Any
from sdfgen import SystemDescription, Sddf, DeviceTree

Arch = SystemDescription.Arch
ProtectionDomain = SystemDescription.ProtectionDomain

class Board:
    def __init__(self, name: str, arch: SystemDescription.Arch, paddr_top: int, timer_device_node: str):
        self.name = name
        self.arch = arch
        self.paddr_top = paddr_top
        self.timer_device_node = timer_device_node


BOARDS: List[Board] = [
    Board("qemu_virt_aarch64", Arch.AARCH64, 0xa_000_000, "timer"),
    Board("odroidc4", Arch.AARCH64, 0x80000000, "soc/bus@ffd00000/watchdog@f0d0"),
    Board("star64", Arch.RISCV64, 0x100000000, "soc/timer@13050000"),
    Board("maaxboard", Arch.AARCH64, 0xa0000000, "soc@0/bus@30000000/timer@302d0000"),
    Board("imx8mm_evk", Arch.AARCH64, 0xa0000000, "soc@0/bus@30000000/timer@302d0000"),
    Board("imx8mp_evk", Arch.AARCH64, 0xa0000000, "soc@0/bus@30000000/timer@302d0000"),
    Board("imx8mq_evk", Arch.AARCH64, 0xa0000000, "soc@0/bus@30000000/timer@302d0000"),
]


def generate_sdf(sdf_file: str, output_dir: str, dtb: DeviceTree):
    timer_driver = ProtectionDomain("timer_driver", "timer_driver.elf", priority=254)
    client = ProtectionDomain("client", "client.elf", priority=1)

    timer_node = dtb.node(board.timer_device_node)
    assert timer_node is not None

    timer_system = Sddf.Timer(sdf, timer_node, timer_driver)
    timer_system.add_client(client)

    pds = [
        timer_driver,
        client
    ]
    for pd in pds:
        sdf.add_pd(pd)

    assert timer_system.connect()
    assert timer_system.serialise_config(output_dir)

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

    board = next(filter(lambda p: p.name == args.board, BOARDS))

    sdf = SystemDescription(board.arch, board.paddr_top)
    sddf = Sddf(args.sddf)

    with open(args.dtb, "rb") as f:
        dtb = DeviceTree(f.read())

    generate_sdf(args.sdf, args.output, dtb)
