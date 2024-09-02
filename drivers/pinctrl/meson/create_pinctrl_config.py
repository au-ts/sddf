# Copyright 2024, UNSW
# SPDX-License-Identifier: BSD-2-Clause

import os
import sys
from devicetree import edtlib, dtlib
import struct

debug_parser = True

def log_normal_parser(print_str: str) -> None:
    if (debug_parser):
        print(print_str)

def log_error_parser(print_str: str) -> None:
    sys.stderr.write(print_str)

if __name__ == "__main__":

    if len(sys.argv) != 5:
        log_error_parser("Usage: ")
        log_error_parser("\tpython3 create_pinmux_setup.py <SoC-name> <dts-source> <pinmux-device-name> <output-dir>")
        exit(1)
    
    # Parse device tree file
    soc_name = sys.argv[1]
    devicetree = dtlib.DT(sys.argv[2], force=True)
    pinmux_node_name = sys.argv[3]
    out_dir = sys.argv[4]

    for node in devicetree.node_iter():
        if pinmux_node_name + "@" in node.name:
            log_normal_parser(f"== mux: {node.name}")

            pinmux_node = node
            for muxed_device_name in pinmux_node.nodes:
                muxed_device_node = pinmux_node.nodes[muxed_device_name]

                if "bank" in muxed_device_name:
                    continue

                log_normal_parser(f"==== device: {muxed_device_node.name}")

                for muxed_device_property_node_name in muxed_device_node.nodes:
                    muxed_device_property_node = muxed_device_node.nodes[muxed_device_property_node_name]

                    log_normal_parser(f"====== property: {muxed_device_property_node.name}")

                    group_names = []
                    function_name = ""
                    bias_enable = -1
                    bias_pullup = -1
                    drive_strength = -1

                    for property_name in muxed_device_property_node.props:
                        if property_name == "groups":
                            group_names = muxed_device_property_node.props[property_name].to_string().split('\0')
                        
                        if property_name == "function":
                            values_list = muxed_device_property_node.props[property_name].to_string().split('\0')
                            if len(values_list) != 1:
                                log_error_parser("looks like your DTS is wrong, you can't have more than two functions for a pin group.\n")
                                exit(1)
                            function_name = values_list[0]

                        if property_name == "bias-disable":
                            bias_enable = False

                        if (property_name == "drive-strength-microamp"):
                            drive_strength = muxed_device_property_node.props[property_name].to_num()
                        
                    if bias_enable == -1:
                        # We haven't encountered the "bias-disable" property
                        if "bias-pull-up" in muxed_device_property_node.props:
                            bias_enable = True
                            bias_pullup = True
                        elif "bias-pull-down" in muxed_device_property_node.props:
                            bias_enable = True
                            bias_pullup = False
                        else:
                            log_error_parser("Warning: bias undefined for device: " + muxed_device_node.name + ". Defaulting to disabling bias!\n")
                            bias_enable = False

                    log_normal_parser(f"group names = {group_names}")
                    log_normal_parser(f"function name = {function_name}")
                    log_normal_parser(f"bias_enable = {bias_enable}")
                    if (bias_enable):
                        if (bias_pullup):
                            log_normal_parser("pull up")
                        else:
                            log_normal_parser("pull down")
                    
                    if drive_strength > 0:
                        log_normal_parser(f"drive strength = {drive_strength}")
