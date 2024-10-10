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
clock_list = {}

def log_normal_parser(print_str: str) -> None:
    if (debug_parser):
        print("PARSER|INFO: " + print_str)

def log_warning_parser(print_str: str) -> None:
    sys.stderr.write("PARSER|WARNING: " + print_str)

def log_error_parser(print_str: str) -> None:
    sys.stderr.write("PARSER|ERROR: " + print_str)

def parse_clock_list(dt: dtlib.DT, clocks: List) -> (List, List):
    pnodes = []
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
            pnodes.append(pnode)
        elif clocks[i] > 0:
            clk_ids.append(clocks[i+1])
            pnodes.append(pnode)
            i += 1
        else:
            clk_ids.append(-1)
        i += 1

    return clk_ids, pnodes

def add_clock(clk_id: int, frequency: int, pclk_id: int):
    if clk_id in clock_list.keys():
        if clock_list[clk_id][0] == 0 and frequency:
            clock_list[clk_id] = (frequency, clock_list[clk_id][1])
        if clock_list[clk_id][1] == 0 and pclk_id:
            clock_list[clk_id] = (clock_list[clk_id][0], pclk_id)
    else:
        clock_list[clk_id] = (frequency, pclk_id)

def extract_clocks(dt: dtlib.DT, node: dtlib.Node) -> List:
    props = list(node.props.keys())
    if "clocks" in props:
        clocks = node.props["clocks"].to_nums()
        clock_ids, pnodes = parse_clock_list(devicetree, clocks)
        for clk_id in clock_ids:
            add_clock(clk_id, 0, 0)
        for pnode in pnodes:
            extract_clocks(dt, pnode)

    if "max-frequency" in props:
        max_frequency = node.props["max-frequency"].to_nums()

    if "assigned-clocks" in props and "assigned-clock-rates" in props:
        assigned_clocks, pnodes = parse_clock_list(devicetree, node.props["assigned-clocks"].to_nums())
        assigned_clock_rates = node.props["assigned-clock-rates"].to_nums()
        for clk_id, clk_rate in zip(assigned_clocks, assigned_clock_rates):
            if (clk_rate):
                add_clock(clk_id, clk_rate, 0)
        for pnode in pnodes:
            extract_clocks(dt, pnode)

    if "assigned-clocks" in props and "assigned-clock-parents" in props:
        assigned_clocks, pnodes = parse_clock_list(devicetree, node.props["assigned-clocks"].to_nums())
        assigned_clock_parents, ppnodes = parse_clock_list(devicetree, node.props["assigned-clock-parents"].to_nums())
        for clk_id, pclk_id in zip(assigned_clocks, assigned_clock_parents):
            if (pclk_id):
                add_clock(clk_id, 0, pclk_id)
        for pnode in pnodes:
            extract_clocks(dt, pnode)
        for pnode in ppnodes:
            extract_clocks(dt, pnode)

    return enabled_clks

def write_configs_to_headerfile(path: str) -> None:
    with open(path + '/clk_config.h', "w") as f:
        f.write("#include <sddf/clk/protocol.h>\n")
        f.write("#define NUM_DEVICE_CLKS {}\n\n".format(len(clock_list)))
        # f.write("#define NUM_DEVICE_CLKS 0\n\n")

        clk_cfg_strs = []
        for key, value in clock_list.items():
            clk_cfg_strs.append("    {{ .clk_id = {}, .frequency = {}, .pclk_id = {} }}".format(key, value[0], value[1]))

        # clk_cfg_strs = ["{{ .clk_id = {}, .frequency = {}, .pclk_id = {} }}".format(clk_cfg[0], clk_cfg[1], clk_cfg[2]) for clk_cfg in clk_configs]
        f.write("static struct clk_cfg clk_configs[] = {{\n{}\n}};".format(",\n".join(clk_cfg_strs)))
        # f.write("static struct clk_cfg clk_configs[] = {};")

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
                extract_clocks(devicetree, node)

    print(clock_list)
    write_configs_to_headerfile(sys.argv[2])
