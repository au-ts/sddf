import argparse
from typing import Dict, List, Any
from sdfgen import SystemDescription, Sddf, DeviceTree

ProtectionDomain = SystemDescription.ProtectionDomain

# TODO: remove platform, it should be board instead to be consistne tiwth Microkit

class Platform:
    def __init__(self, name: str, arch: SystemDescription.Arch, paddr_top: int, timer_device_node: str):
        self.name = name
        self.arch = arch
        self.paddr_top = paddr_top
        self.timer_device_node = timer_device_node


PLATFORMS: List[Platform] = [
    Platform("qemu_virt_aarch64", SystemDescription.Arch.AARCH64, 0xa_000_000, "timer"),
    Platform("odroidc4", SystemDescription.Arch.AARCH64, 0x80000000, "soc/bus@ffd00000/watchdog@f0d0"),
    Platform("star64", SystemDescription.Arch.RISCV64, 0x100000000, "soc/timer@13050000"),
    Platform("maaxboard", SystemDescription.Arch.AARCH64, 0xa0000000, "soc@0/bus@30000000/timer@302d0000"),
]


def generate_sdf(output: str, dtb: DeviceTree):
    timer_driver = ProtectionDomain("timer_driver", "timer_driver.elf", priority=200)
    client = ProtectionDomain("client", "client.elf", priority=1)

    timer_node = dtb.node(platform.timer_device_node)
    assert timer_node is not None

    timer_system = Sddf.Timer(sdf, timer_node, timer_driver)
    timer_system.add_client(client)

    pds = [
        timer_driver,
        client
    ]
    for pd in pds:
        sdf.add_pd(pd)

    timer_system.connect()
    timer_system.serialise_config(output)

    with open(output + "/timer.system", "w+") as f:
        f.write(sdf.xml())


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument("--dtbs", required=True)
    parser.add_argument("--sddf", required=True)
    parser.add_argument("--platform", required=True, choices=[p.name for p in PLATFORMS])
    parser.add_argument("--output", required=True)

    args = parser.parse_args()

    platform = next(filter(lambda p: p.name == args.platform, PLATFORMS))

    sdf = SystemDescription(platform.arch, platform.paddr_top)
    sddf = Sddf(args.sddf)

    with open(args.dtbs + f"/{platform.name}.dtb", "rb") as f:
        dtb = DeviceTree(f.read())

    generate_sdf(args.output, dtb)
