#!/usr/bin/env python3

# Copyright 2024, UNSW
# SPDX-License-Identifier: BSD-2-Clause
#
# The template is stolen from Bill's pinmux driver

import os
import sys
from typing import List
from devicetree import edtlib, dtlib

supported_compat_str_board = { "hardkernel,odroid-c4" }

debug_parser = True

def log_normal_parser(print_str: str) -> None:
    if (debug_parser):
        print("PARSER|INFO: " + print_str)

def log_warning_parser(print_str: str) -> None:
    sys.stderr.write("PARSER|WARNING: " + print_str)

def log_error_parser(print_str: str) -> None:
    sys.stderr.write("PARSER|ERROR: " + print_str)

def parse_clocks(dt: dtlib.DT, clocks: List) -> List:
    clk_ids = []
    i = 0

    while (i < len(clocks)):
        if clocks[i] == 0:
            clk_ids.append(clocks[i])
            i += 1
            continue
        pnode = devicetree.phandle2node[clocks[i]]
        if "#clock-cells" in pnode.props and pnode.props["#clock-cells"].to_num() == 0:
            # TODO: consider the case of `xtal` and represent this clock another way
            clk_ids.append(clocks[i])
        elif clocks[i] > 0:
            clk_ids.append(clocks[i+1])
            i += 1
        else:
            clk_ids.append(-1)
        i += 1

    return clk_ids;

def write_configs_to_headerfile(path: str, clk_configs: List) -> None:
    with open(path + '/clk_config.h', "w") as f:
        f.write("#include <conf_types.h>\n")
        f.write("#define NUM_DEVICE_CLKS {}\n\n".format(len(clk_configs)))

        clk_cfg_strs = ["{{ .clk_id = {}, .frequency = {}, .pclk_id = {} }}".format(clk_cfg[0], clk_cfg[1], clk_cfg[2]) for clk_cfg in clk_configs]
        f.write("static struct clk_cfg clk_configs[] = {{\n{}\n}};".format(",\n".join(clk_cfg_strs)))

if __name__ == "__main__":
    print("Creating a config file for clock driver to intialise the system...")

    devicetree = dtlib.DT(sys.argv[1], force=True)
    for compat_str in devicetree.root.props["compatible"].to_strings():
        if compat_str in supported_compat_str_board:
            supported = True
            break

    if not supported:
        log_error_parser("this board is not supported.")
        exit(1)

    enabled_clks = []

    for node in devicetree.node_iter():
        props = list(node.props.keys())
        if "status" in props:
            status = node.props["status"].to_string()
            if status == "okay":
                clocks = []
                max_frequency = []
                assigned_clocks = []
                assigned_clock_parents = []
                assigned_clock_rates = []
                print("---------------------")
                if "clocks" in props:
                    clocks = node.props["clocks"].to_nums()
                    clock_ids = parse_clocks(devicetree, clocks)
                    for clk_id in clock_ids:
                        enabled_clks.append([clk_id, 0, 0])
                if "max-frequency" in props:
                    max_frequency = node.props["max-frequency"].to_nums()

                if "assigned-clocks" in props and "assigned-clock-rates" in props:
                    assigned_clocks = parse_clocks(devicetree, node.props["assigned-clocks"].to_nums())
                    assigned_clock_rates = node.props["assigned-clock-rates"].to_nums()
                    for clk_id, clk_rate in zip(assigned_clocks, assigned_clock_rates):
                        if (clk_rate):
                            enabled_clks.append([clk_id, clk_rate, 0])
                        print("rate: <{}, {}>".format(clk_id, clk_rate))

                if "assigned-clocks" in props and "assigned-clock-parents" in props:
                    assigned_clocks = parse_clocks(devicetree, node.props["assigned-clocks"].to_nums())
                    assigned_clock_parents = parse_clocks(devicetree, node.props["assigned-clock-parents"].to_nums())
                    for clk_id, pclk_id in zip(assigned_clocks, assigned_clock_parents):
                        print(f"pclk: <{clk_id}, {pclk_id}>")
                        if (pclk_id):
                            enabled_clks.append([clk_id, 0, pclk_id])

                print("{}\nclocks: {}\nmax-frequency: {}\nassigned-clocks: {}\nassigned-clock-parents: {}\nassigned-clock-rates: {}".format(
                    node.name,
                    clocks,
                    max_frequency,
                    assigned_clocks,
                    assigned_clock_parents,
                    assigned_clock_rates)
                )

    write_configs_to_headerfile(sys.argv[2], enabled_clks)
