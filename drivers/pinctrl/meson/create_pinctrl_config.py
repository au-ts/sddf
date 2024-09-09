# Copyright 2024, UNSW
# SPDX-License-Identifier: BSD-2-Clause

# This script only works with Device Tree Source (DTS) file for Odroid C4
# If you only have a compiled DTB, you can decompile it into a DTS with:
# $ dtc -I dtb -O dts -o input.dtb output.dts

# A typical invocation might look like:
# $ python3 create_pinctrl_config.py hardkernel,odroid-c4 your_device_tree.dts build 

import os
import sys
import re
from devicetree import edtlib, dtlib
import struct

from odroidc4 import *

supported_compat_str_board = { "hardkernel,odroid-c4" }

debug_parser = True

def log_normal_parser(print_str: str) -> None:
    if (debug_parser):
        print("PARSER|INFO: " + print_str)

def log_warning_parser(print_str: str) -> None:
    sys.stderr.write("PARSER|WARNING: " + print_str)

def log_error_parser(print_str: str) -> None:
    sys.stderr.write("PARSER|ERROR: " + print_str)



# Each mux data node inside the DTS is represented with this class.
class PinData:
    def __init__(self, 
                 muxed_device_name: str, 
                 muxed_device_property_node_name: str, 
                 group_names: list[str], 
                 function_name: str, 
                 bias_enable: bool, 
                 bias_pullup: bool, 
                 drive_strength: int):
        
        # for debugging: name of the device in DTS
        self.muxed_device_name = muxed_device_name
        # for debugging: name of the mux subproperty
        self.muxed_device_property_node_name = muxed_device_property_node_name

        self.group_names = group_names
        self.function_name = function_name
        self.bias_enable = bias_enable
        self.bias_pullup = bias_pullup       # Ignore if bias_enable is False
        self.drive_strength = drive_strength # <0 for input pads

    def __str__(self):
        representation = f"Property {self.muxed_device_property_node_name} of {self.muxed_device_name}\n"
        representation += f"\tGroups: {str(self.group_names)}\n"
        representation += f"\tFunction: {str(self.function_name)}\n"
        representation += f"\tBias?: "

        if (self.bias_enable):
            if (self.bias_pullup):
                representation += "pull-up\n"
            else:
                representation += "pull-down\n"
        else:
            representation += "no\n"

        representation += f"\tDrive-strength: {str(self.drive_strength)}\n"

        return representation

# This function extract pinmux data from the "pinctrl" node in DTS and return a list of PinData.
# It will be called twice, once for peripherals and always-on GPIO chips.
def get_pinctrl_data(pinmux_node, enabled_phandles): 
    # `pinmux_node` looks something like this:
    # pinctrl@40 {
    #     compatible = "amlogic,meson-g12a-periphs-pinctrl";
    #     #address-cells = <0x02>;
    #     #size-cells = <0x02>;
    #     ranges;
    #     phandle = <0x19>;

    #     bank@40 {
    #         ...
    #     };

    #     cec_ao_a_h {
    #         phandle = <0x1a>;
    #         mux {
    #             groups = "cec_ao_a_h";
    #             function = "cec_ao_a_h";
    #             bias-disable;
    #         };
    #     };

    result = []
    for muxed_device_name in pinmux_node.nodes:
        muxed_device_node = pinmux_node.nodes[muxed_device_name]

        if "bank" in muxed_device_name:
            # We don't care about the bank node because it just have the registers sizes.
            continue

        if "phandle" in muxed_device_node.props.keys() and hex(muxed_device_node.props["phandle"].to_num()) in enabled_phandles:
            enabled_phandles[hex(muxed_device_node.props["phandle"].to_num())] = True
            for muxed_device_property_node_name in muxed_device_node.nodes:
                # Each device can have multiple mux properties of it's different ports.
                # E.g. an emmc_cmd port need pull up, whereas an emmc_clk does not need bias at all

                muxed_device_property_node = muxed_device_node.nodes[muxed_device_property_node_name]

                # These variables are what we care about
                group_names = []
                function_name = ""
                bias_enable = -1
                bias_pullup = -1
                drive_strength = -1

                for subproperty_name in muxed_device_property_node.props:
                    if subproperty_name == "groups":
                        group_names = muxed_device_property_node.props[subproperty_name].to_string().split('\0')
                    
                    if subproperty_name == "function":
                        values_list = muxed_device_property_node.props[subproperty_name].to_string().split('\0')
                        if len(values_list) != 1:
                            log_error_parser("looks like your DTS is wrong, you can't have more than two functions for a pin group.\n")
                            exit(1)
                        function_name = values_list[0]

                    if subproperty_name == "bias-disable":
                        bias_enable = False

                    if subproperty_name == "drive-strength-microamp":
                        drive_strength = muxed_device_property_node.props[subproperty_name].to_num()
                    
                if bias_enable == -1:
                    # We haven't encountered the "bias-disable" property
                    if "bias-pull-up" in muxed_device_property_node.props:
                        bias_enable = True
                        bias_pullup = True
                    elif "bias-pull-down" in muxed_device_property_node.props:
                        bias_enable = True
                        bias_pullup = False
                    else:
                        log_warning_parser("Warning: bias undefined for device: " + muxed_device_node.name + ". Defaulting to disabling bias!\n")
                        bias_enable = False
                
                result.append(PinData(muxed_device_name, muxed_device_property_node_name, group_names, function_name, bias_enable, bias_pullup, drive_strength))

    return result


if __name__ == "__main__":
    if len(sys.argv) != 4:
        log_error_parser("Usage: ")
        log_error_parser("\tpython3 create_pinmux_setup.py <SoC-name> <dts-source> <output-dir>")
        exit(1)
    
    # Parse device tree file
    soc_name = sys.argv[1]
    devicetree = dtlib.DT(sys.argv[2], force=True)
    pinmux_node_name = "pinctrl@"
    out_dir = sys.argv[3]
    
    # Check compatibility
    supported = False
    for compat_str in devicetree.root.props["compatible"].to_strings():
        if compat_str in supported_compat_str_board:
            supported = True
            break
    if not supported:
        log_error_parser("this board is not supported.")
        exit(1)

    # Only parse devices that are enabled.
    # Set of pinctrl phandles we care about, hex represented as string, value is whether the phandle has been
    #    encountered in later parsing steps.
    enabled_phandles: dict[str, bool] = {}
    for node in devicetree.node_iter():
        if "status" in node.props and node.props["status"].to_string() == "okay":
            for prop_name in node.props.keys():
                if re.match(r"^pinctrl-[0-9]+$", prop_name):
                    for phandle in node.props[prop_name].to_nums():
                        if phandle in enabled_phandles:
                            log_error_parser(f"duplicate pinctrl phandle: {hex(phandle)}")
                            exit(1)
                        else:
                            enabled_phandles[hex(phandle)] = False
    
    log_normal_parser("Enabled devices found: " + str(enabled_phandles))

    # Read actual pinmux data
    peripherals_dts_data: list[PinData] = []
    ao_dts_data: list[PinData] = []

    for node in devicetree.node_iter():
        if pinmux_node_name in node.name:
            pinmux_node = node
            if pinmux_node.props["compatible"].to_string() == "amlogic,meson-g12a-periphs-pinctrl":
                peripherals_dts_data = get_pinctrl_data(pinmux_node, enabled_phandles)
            elif pinmux_node.props["compatible"].to_string() == "amlogic,meson-g12a-aobus-pinctrl":
                ao_dts_data = get_pinctrl_data(pinmux_node, enabled_phandles)
            else:
                log_error_parser("encountered unsupported pinmux node.")
                exit(1)

    log_normal_parser("Peripherals:\n")
    for pin in peripherals_dts_data:
        log_normal_parser(str(pin))

    log_normal_parser("AO\n")
    for pin in ao_dts_data:
        log_normal_parser(str(pin))

    for phandle, processed in enabled_phandles.items():
        if not processed:
            log_error_parser(f"phandle {phandle} does not have any configuration data in DTS")
            exit(1)

    # Map pinmux data from DTS to memory values
    dts_data = peripherals_dts_data
    func_to_group_map = function_to_group
    pad_to_idx_map = pad_to_idx
    port_to_pad_map = port_to_pad
    port_to_mux_func_map = port_to_mux_func

    encountered_pad = set()
    for pindata in dts_data:
        for port in pindata.group_names:
            this_port_function_group: str = pindata.function_name
            if port not in func_to_group_map[this_port_function_group]:
                log_error_parser(f"the function group {this_port_function_group} does not contain port {port}")
                exit(1)
            else:
                pad_idx = -1
                mux_func = -1
                if pindata.function_name == "gpio_periphs":
                    # Special case where the pad is not connected to any port and is used as a GPIO
                    pad_idx = pad_to_idx_map[port]
                    mux_func = 0
                else:
                    pad_idx = port_to_pad_map[port]
                    mux_func = port_to_mux_func_map[port]

                if pad_idx in encountered_pad:
                    log_error_parser(f"the pad {pad_idx} has been muxed twice!")
                    exit(1)
                else:
                    encountered_pad.add(pad_idx)

    # Write to assembly file
    with open(out_dir + "/pinctrl_config_data.s", "w") as file:
        file.write(".section .data\n")
        file.write("\t.align 4\n")

