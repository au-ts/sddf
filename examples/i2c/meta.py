import argparse
from typing import Dict, List, Any
from sdfgen import SystemDescription, Sddf, DeviceTree

ProtectionDomain = SystemDescription.ProtectionDomain
MemoryRegion = SystemDescription.MemoryRegion
Map = SystemDescription.Map


class Platform:
    def __init__(self, name: str, arch: SystemDescription.Arch, paddr_top: int, i2c_device_node: str, timer_device_node: str):
        self.name = name
        self.arch = arch
        self.paddr_top = paddr_top
        self.i2c_device_node = i2c_device_node
        self.timer_device_node = timer_device_node


PLATFORMS: List[Platform] = [
    Platform("odroidc4", SystemDescription.Arch.AARCH64, 0x80000000, "soc/bus@ffd00000/i2c@1d000", "soc/bus@ffd00000/watchdog@f0d0"),
]

def generate_sdf(sdf_file: str, output_dir: str, dtb: DeviceTree):
    timer_driver = ProtectionDomain("timer_driver", "timer_driver.elf", priority=4)
    i2c_driver = ProtectionDomain("i2c_driver", "i2c_driver.elf", priority=3)
    i2c_virt = ProtectionDomain("i2c_virt", "i2c_virt.elf", priority=2)
    client_pn532 = ProtectionDomain("client_pn532", "client_pn532.elf", priority=1)
    client_ds3231 = ProtectionDomain("client_ds3231", "client_ds3231.elf", priority=1)

    clk_mr = MemoryRegion("clk", 0x1000, paddr=0xff63c000)
    gpio_mr = MemoryRegion("gpio", 0x1000, paddr=0xff634000)
    sdf.add_mr(clk_mr)
    sdf.add_mr(gpio_mr)

    i2c_driver.add_map(Map(clk_mr, 0x30_000_000, Map.Perms(r=True, w=True), cached=False))
    i2c_driver.add_map(Map(gpio_mr, 0x30_100_000, Map.Perms(r=True, w=True), cached=False))

    i2c_node = dtb.node(platform.i2c_device_node)
    assert i2c_node is not None
    timer_node = dtb.node(platform.timer_device_node)
    assert timer_node is not None

    i2c_system = Sddf.I2c(sdf, i2c_node, i2c_driver, i2c_virt)
    i2c_system.add_client(client_pn532)
    i2c_system.add_client(client_ds3231)

    timer_system = Sddf.Timer(sdf, timer_node, timer_driver)
    timer_system.add_client(client_pn532)
    timer_system.add_client(client_ds3231)

    pds = [
        timer_driver,
        i2c_driver,
        i2c_virt,
        client_pn532,
        client_ds3231,
    ]
    for pd in pds:
        sdf.add_pd(pd)

    assert i2c_system.connect()
    assert i2c_system.serialise_config(output_dir)
    assert timer_system.connect()
    assert timer_system.serialise_config(output_dir)

    with open(f"{output_dir}/{sdf_file}", "w+") as f:
        f.write(sdf.xml())


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument("--dtbs", required=True)
    parser.add_argument("--sddf", required=True)
    parser.add_argument("--platform", required=True, choices=[p.name for p in PLATFORMS])
    parser.add_argument("--output", required=True)
    parser.add_argument("--sdf", required=True)

    args = parser.parse_args()

    platform = next(filter(lambda p: p.name == args.platform, PLATFORMS))

    sdf = SystemDescription(platform.arch, platform.paddr_top)
    sddf = Sddf(args.sddf)

    with open(args.dtbs + f"/{platform.name}.dtb", "rb") as f:
        dtb = DeviceTree(f.read())

    generate_sdf(args.sdf, args.output, dtb)
