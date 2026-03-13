# Copyright 2026, UNSW
# SPDX-License-Identifier: BSD-2-Clause
import os, sys
import argparse
from typing import List
from dataclasses import dataclass
from sdfgen import SystemDescription, Sddf, DeviceTree
from importlib.metadata import version

sys.path.append(
    os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../tools/meta")
)
from board import BOARDS

assert version("sdfgen").split(".")[1] == "29", "Unexpected sdfgen version"

ProtectionDomain = SystemDescription.ProtectionDomain
MemoryRegion = SystemDescription.MemoryRegion
Map = SystemDescription.Map
Channel = SystemDescription.Channel
IrqConventional = SystemDescription.IrqConventional


def generate(sdf_file: str, output_dir: str, dtb: DeviceTree):
    serial_driver = ProtectionDomain("serial_driver", "serial_driver.elf", priority=200)
    # Increase the stack size as running with UBSAN uses more stack space than normal.
    serial_virt_tx = ProtectionDomain(
        "serial_virt_tx", "serial_virt_tx.elf", priority=199, stack_size=0x2000
    )

    # pinctrl must be higher prio than everything
    # timer driver should be highest next highest prio for sanity
    # i2c must be higher priority than pmic
    # pmic must be higher priority than dvfs
    # clk must be higher prio than dvfs
    # pwm must be higher prio than client
    # tmu must be higher prio than client
    pinctrl_driver = ProtectionDomain(
        "pinctrl_driver", "pinctrl_driver.elf", priority=253
    )
    timer_driver = ProtectionDomain("timer_driver", "timer_driver.elf", priority=200)
    clk_driver = ProtectionDomain("clk_driver", "clk_driver.elf", priority=110, passive=True)
    i2c_driver = ProtectionDomain("i2c_driver", "i2c_driver.elf", priority=102)
    i2c_virt = ProtectionDomain("i2c_virt", "i2c_virt.elf", priority=101)
    pmic_driver = ProtectionDomain("pmic_driver", "pmic_driver.elf", priority=100)
    dvfs_driver = ProtectionDomain("dvfs_driver", "dvfs_driver.elf", priority=99, passive=True)
    pwm_driver = ProtectionDomain("pwm_driver", "pwm_driver.elf", priority=98)
    tmu_driver = ProtectionDomain("tmu_driver", "tmu_driver.elf", priority=97, passive=True)
    thermal_control = ProtectionDomain("thermal_control", "thermal_control.elf", priority=2)
    worker = ProtectionDomain("worker", "worker.elf", priority=1)


    timer_node = dtb.node(board.timer)
    assert timer_node is not None
    serial_node = dtb.node(board.serial)
    assert serial_node is not None
    i2c_node = dtb.node(board.i2c)
    assert i2c_node is not None
    pinctrl_node = dtb.node(board.pinctrl)
    assert pinctrl_node is not None

    timer_system = Sddf.Timer(sdf, timer_node, timer_driver)
    timer_system.add_client(thermal_control)
    serial_system = Sddf.Serial(
        sdf, serial_node, serial_driver, serial_virt_tx, enable_color=False
    )
    serial_system.add_client(thermal_control)
    serial_system.add_client(worker)

    i2c_system = Sddf.I2c(sdf, i2c_node, i2c_driver, i2c_virt)
    i2c_system.add_client(pmic_driver)

    pinctrl_system = Sddf.Pinctrl(sdf, pinctrl_node, pinctrl_driver)

    # HACK: sdfgen doesn't support multiple regions for a device resource yet
    #       or the clk class. This will be removed in the pending sdfgen refactor.
    #       We can add direct support for the Maaxboard via boards.py, but
    #       the odroid clk driver depends on numerous maps that aren't in the DTS
    #       at all, meaning this switch is the best we can do for now.
    regions = []    # tuples of (mr, map var name)
    if board.name == "maaxboard":
        clk_ccm_mr = MemoryRegion(sdf, "clk_ccm", 0xd000, paddr=0x30380000)
        clk_ccm_analog_mr = MemoryRegion(sdf, "clk_ccm_analog", 0x1000, paddr=0x30360000)
        sdf.add_mr(clk_ccm_mr)
        sdf.add_mr(clk_ccm_analog_mr)

        clk_ccm_map = Map(clk_ccm_mr, 0x3200000, "rw", cached=False)
        clk_ccm_analog_map = Map(clk_ccm_analog_mr, 0x3300000, "rw", cached=False)
        clk_driver.add_map(clk_ccm_map)
        clk_driver.add_map(clk_ccm_analog_map)
        # HACK for sdfgen.             "soc@0/bus@30400000/pwm@30670000",
        pwm1_mr = MemoryRegion(sdf, "pwm1", 0x10_000, paddr=0x30660000)
        pwm2_mr = MemoryRegion(sdf, "pwm2", 0x10_000, paddr=0x30670000)
        pwm3_mr = MemoryRegion(sdf, "pwm3", 0x10_000, paddr=0x30680000)
        pwm4_mr = MemoryRegion(sdf, "pwm4", 0x10_000, paddr=0x30690000)
        sdf.add_mr(pwm1_mr)
        sdf.add_mr(pwm2_mr)
        sdf.add_mr(pwm3_mr)
        sdf.add_mr(pwm4_mr)
        pwm_driver.add_map(Map(pwm1_mr, 0x30_000_000, "rw", cached=False))
        pwm_driver.add_map(Map(pwm2_mr, 0x30_010_000, "rw", cached=False))
        pwm_driver.add_map(Map(pwm3_mr, 0x30_020_000, "rw", cached=False))
        pwm_driver.add_map(Map(pwm4_mr, 0x30_030_000, "rw", cached=False))
        # Despite having IRQs, we never need them.
        # pwm_driver.add_irq(IrqConventional(0x52 + 32, IrqConventional.Trigger.LEVEL))
        # pwm_driver.add_irq(IrqConventional(0x53 + 32, IrqConventional.Trigger.LEVEL))
        # pwm_driver.add_irq(IrqConventional(0x54 + 32, IrqConventional.Trigger.LEVEL))
        # pwm_driver.add_irq(IrqConventional(0x55 + 32, IrqConventional.Trigger.LEVEL))
        tmu_mr = MemoryRegion(sdf, "tmu_mr", 0x1000, paddr=0x30260000)
        sdf.add_mr(tmu_mr)

        tmu_mr_map = Map(tmu_mr, 0x30260000, "rw", cached=False)
        tmu_driver.add_map(tmu_mr_map)
        tmu_driver.add_irq(IrqConventional(49 + 32, IrqConventional.Trigger.EDGE))


    else:
        print("Unsupported board!")
        exit(-1)


    # add channels
    # TODO: replace with sdfgen invocations
    clk_channel_dvfs = Channel(clk_driver, dvfs_driver, pp_b=True)
    sdf.add_channel(clk_channel_dvfs)

    clk_channel_pwm = Channel(clk_driver, pwm_driver, pp_b=True)
    sdf.add_channel(clk_channel_pwm)
    assert clk_channel_pwm.pd_b_id == 0, clk_channel_pwm.pd_b_id

    pmic_channel = Channel(pmic_driver, dvfs_driver, pp_b=True)
    sdf.add_channel(pmic_channel)

    dvfs_channel = Channel(dvfs_driver, thermal_control, pp_b=True)
    sdf.add_channel(dvfs_channel)

    pwm_channel = Channel(pwm_driver, thermal_control, pp_b=True, notify_a=False, notify_b=False)
    sdf.add_channel(pwm_channel)

    tmu_channel = Channel(tmu_driver, thermal_control, pp_b=True)
    sdf.add_channel(tmu_channel)

    pds = [
        dvfs_driver,
        clk_driver,
        pwm_driver,
        tmu_driver,
        pinctrl_driver,
        serial_driver,
        serial_virt_tx,
        timer_driver,
        pmic_driver,
        i2c_driver,
        i2c_virt,
        thermal_control,
        worker
    ]
    for pd in pds:
        sdf.add_pd(pd)

    assert i2c_system.connect()
    assert i2c_system.serialise_config(output_dir)
    assert serial_system.connect()
    assert serial_system.serialise_config(output_dir)
    assert timer_system.connect()
    assert timer_system.serialise_config(output_dir)
    assert pinctrl_system.connect()
    assert pinctrl_system.serialise_config(output_dir)

    with open(f"{output_dir}/{sdf_file}", "w+") as f:
        f.write(sdf.render())


if __name__ == "__main__":
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

    generate(args.sdf, args.output, dtb)
