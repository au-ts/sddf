# Copyright 2024, UNSW
# SPDX-License-Identifier: BSD-2-Clause

# Only works with device tree source files found in https://github.com/seL4/seL4/tree/master/tools/dts

# A typical invocation might look like:
# $ python3 create_pinctrl_config.py hardkernel,odroid-c4 ../../../examples/pinctrl/serial_redirect/dts/odroidc4.dts build 

import os
import sys
from devicetree import edtlib, dtlib
import struct

supported_compat_str_board = { "hardkernel,odroid-c4" }

debug_parser = True

def log_normal_parser(print_str: str) -> None:
    if (debug_parser):
        print("PARSER|INFO: " + print_str)

def log_warning_parser(print_str: str) -> None:
    sys.stderr.write("PARSER|WARNING: " + print_str)

def log_error_parser(print_str: str) -> None:
    sys.stderr.write("PARSER|ERROR: " + print_str)

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
        self.drive_strength = drive_strength # <0 for output pads

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

def get_pinctrl_data(pinmux_node): 
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

        for muxed_device_property_node_name in muxed_device_node.nodes:
            # Each device can have multiple mux properties it's different ports.
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

    # Read actual pinmux data
    peripherals_dts_data = []
    ao_dts_data = []

    for node in devicetree.node_iter():
        if pinmux_node_name in node.name:
            pinmux_node = node
            if pinmux_node.props["compatible"].to_string() == "amlogic,meson-g12a-periphs-pinctrl":
                peripherals_dts_data = get_pinctrl_data(pinmux_node)
            elif pinmux_node.props["compatible"].to_string() == "amlogic,meson-g12a-aobus-pinctrl":
                ao_dts_data = get_pinctrl_data(pinmux_node)
            else:
                log_error_parser("encountered unsupported pinmux node.")
                exit(1)
    
    # log_normal_parser("Peripherals:\n")
    # for pin in peripherals_dts_data:
    #     print(str(pin))
    
    # log_normal_parser("AO\n")
    # for pin in ao_dts_data:
    #     print(str(pin))

    # Map pinmux data from DTS to memory values
