import argparse
from typing import Dict, List, Any
from sdfgen import SystemDescription, ProtectionDomain, Sddf, DeviceTree


class Platform:
    def __init__(self, name: str, arch: SystemDescription.Arch, paddr_top: int, i2c_device_node: str):
        self.name = name
        self.arch = arch
        self.paddr_top = paddr_top
        self.i2c_device_node = i2c_device_node


PLATFORMS: List[Platform] = [
    Platform("odroidc4", SystemDescription.Arch.AARCH64, 0x80000000, "soc/bus@ffd00000/i2c@1d000"),
]

def generate_sdf():
    i2c_driver = ProtectionDomain("i2c_driver", "i2c_driver.elf", priority=3)
    i2c_virt = ProtectionDomain("i2c_virt", "i2c_virt.elf", priority=2)
    client = ProtectionDomain("client", "client.elf", priority=1)

    i2c_node = dtb.node(platform.i2c_device_node)
    assert i2c_node is not None

    i2c_system = Sddf.I2c(sdf, i2c_node, i2c_driver, i2c_virt)
    i2c_system.add_client(client)

    pds = [
        i2c_driver,
        i2c_virt,
        client
    ]
    for pd in pds:
        sdf.add_pd(pd)

    i2c_system.connect()

    with open(output + "/i2c.system", "w+") as f:
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

    generate_sdf()
