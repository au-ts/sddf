#!/usr/bin/env python3

# Copyright 2024, UNSW
# SPDX-License-Identifier: BSD-2-Clause
#
# The template is stolen from Bill's pinmux driver

import os
import sys

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
                if "clocks" in props:
                    clocks = node.props["clocks"].to_nums()
                if "max-frequency" in props:
                    max_frequency = node.props["max-frequency"].to_nums()
                if "assigned-clocks" in props:
                    assigned_clocks = node.props["assigned-clocks"].to_nums()
                if "assigned-clock-parents" in props:
                    assigned_clock_parents = node.props["assigned-clock-parents"].to_nums()
                if "assigned-clock-rates" in props:
                    assigned_clock_rates = node.props["assigned-clock-rates"].to_nums()
                print("{} - clocks: {}, max-frequency: {}, assigned-clocks: {}, assigned-clock-parents: {}, assigned-clock-rates: {}".format(
                    node.name,
                    clocks,
                    max_frequency,
                    assigned_clocks,
                    assigned_clock_parents,
                    assigned_clock_rates)
                )
