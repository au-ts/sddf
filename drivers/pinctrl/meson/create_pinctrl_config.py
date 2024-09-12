# Copyright 2024, UNSW
# SPDX-License-Identifier: BSD-2-Clause

# This script only works with Device Tree Source (DTS) file for Odroid C4
# If you only have a compiled DTB, you can decompile it into a DTS with:
# $ dtc -I dtb -O dts -o input.dtb output.dts

# A typical invocation might look like:
# $ python3 create_pinctrl_config.py hardkernel,odroid-c4 your_device_tree.dts build 

import sys
sys.dont_write_bytecode = True

import os
import re
from devicetree import edtlib, dtlib
import struct
from collections import OrderedDict

##### LOGGING
debug_parser = True

def log_normal_parser(print_str: str) -> None:
    if (debug_parser):
        print("PARSER|INFO: " + print_str)

def log_warning_parser(print_str: str) -> None:
    sys.stderr.write("PARSER|WARNING: " + print_str)

def log_error_parser(print_str: str) -> None:
    sys.stderr.write("PARSER|ERROR: " + print_str)

##### COMPATIBILITY CHECKING
supported_compat_str_board = { "hardkernel,odroid-c4" }

def is_dts_compatible(devicetree: dtlib.DT) -> None:
    supported = False
    for compat_str in devicetree.root.props["compatible"].to_strings():
        if compat_str in supported_compat_str_board:
            supported = True
            break
    if not supported:
        log_error_parser("this board is not supported.")
        exit(1)

##### DTS SANITISATION

# Given the device tree, extract any devices that are enabled (prop status = "okay")
# and have pinctrl phandles. Returns a dict of phandle int -> device name for debugging.
def fetch_enabled_devices(devicetree: dtlib.DT) -> dict[int, str]:
    enabled_phandles: dict[int, str] = {}
    for node in devicetree.node_iter():
        if "status" in node.props and node.props["status"].to_string() == "okay":
            if "pinctrl-0" in node.props.keys():
                for phandle in node.props["pinctrl-0"].to_nums():
                    if phandle in enabled_phandles:
                        log_error_parser(f"duplicate pinctrl phandle: {hex(phandle)}")
                        exit(1)
                    else:
                        enabled_phandles[phandle] = node.name

    return enabled_phandles

##### PINCTRL DATA REPRESENTATION

# Each pinctrl data node inside the DTS is represented with this class.
# These data are then converted into memory values for writing into pinmux registers.
class PinData:
    def __init__(self, 
                 phandle: int,
                 muxed_device_name: str, 
                 muxed_device_property_node_name: str, 
                 group_names: list[str], 
                 function_name: str, 
                 bias_enable: bool, 
                 bias_pullup: bool, 
                 drive_strength: int):
        
        self.phandle = phandle
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

##### PINCTRL DATA EXTRACTION

# This function extract pinmux data from the "pinctrl" node in DTS and return a list of PinData.
# It will be called twice, once for peripherals and always-on GPIO chips.
# Returns a list of PinData.
def get_pinctrl_data(pinmux_node: dtlib.Node, enabled_phandles: dict[int, str]) -> list[PinData]: 
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

    result: list[PinData] = []
    for muxed_device_name in pinmux_node.nodes:
        muxed_device_node = pinmux_node.nodes[muxed_device_name]

        if "bank" in muxed_device_name:
            # We don't care about the bank node because it just have the registers sizes.
            continue

        if "phandle" in muxed_device_node.props.keys() and muxed_device_node.props["phandle"].to_num() in enabled_phandles:
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
                
                result.append(PinData(muxed_device_node.props["phandle"].to_num(), 
                                      muxed_device_name, 
                                      muxed_device_property_node_name, 
                                      group_names, 
                                      function_name, 
                                      bias_enable, 
                                      bias_pullup, 
                                      drive_strength)
                )

    return result

##### BITS UTIL
def zero_n_bits_at_ith_bit_of_32bits(register: int, n: int, ith: int) -> int:
    if n < 0 or ith < 0 or register > 0xFFFF_FFFF:
        log_error_parser(f"invalid arg to zero_n_bits_at_ith_bit: register = {register}, n = {n}, ith = {ith}\n")
        exit(1)
    
    mask = 0xFFFF_FFFF
    mask = mask >> (ith + n)

    for i in range(n):
        mask = mask << 1
    
    for i in range(ith):
        mask = mask << 1
        mask |= 1
    
    result = register & mask
    if result > 0xFFFF_FFFF:
        log_error_parser(f"bad output zero_n_bits_at_ith_bit_of_32bits(register={hex(register)}, n={n}, ith={ith}) = {hex(result)}")
        exit(1)

    return result

##### MEMORY
def pindata_to_register_values(
    # Input
    dts_data,
    func_to_group_map,
    pad_to_idx_map,
    port_to_pad_map,
    port_to_mux_func_map,

    # Output
    mux_registers,
    ds_registers,
    bias_en_registers,
    pull_dir_registers
) -> None:
    encountered_pad = set()
    pindata: PinData
    for pindata in dts_data:
        # Each pindata properties can contain settings for a group of pins
        for port in pindata.group_names:
            # For each pin and the attached common function, work out the appropriate muxing data
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

                if mux_func < 0 or mux_func > 7:
                    log_error_parser(f"the pad {pad_idx} have an invalid mux value: {mux_func}")
                    exit(1)

                # Work out which mux register this pad is in
                found = False
                for reg in mux_registers:
                    if pad_idx >= reg["first_pad"] and pad_idx <= reg["last_pad"]:
                        found = True

                        nth_pin = pad_idx - reg["first_pad"]    # in the bank
                        nth_bit = nth_pin * reg["bits_per_pin"] # in the bank

                        # Fetch the bank value then zero out the bits that belong to this pad
                        zeroed_regval = zero_n_bits_at_ith_bit_of_32bits(reg["value"], reg["bits_per_pin"], nth_bit)
                        
                        # Prepare mux setting value to be OR'ed into the zeroed out slot
                        data_mask = mux_func << nth_bit

                        log_normal_parser(f"pad #{pad_idx} was given mux func {mux_func}, prev reg is {hex(reg["value"])}, ")

                        reg["value"] = zeroed_regval | data_mask

                        log_normal_parser(f"after reg is {hex(reg["value"])}\n")

                        break

                if not found:
                    log_error_parser(f"cannot find the pin bank that the port {port} belongs in for muxing\n")
                    exit(1)

                # Then work out the biasing (if any)
                found = False
                bias_enabled = False
                for reg in bias_en_registers:
                    if pad_idx >= reg["first_pad"] and pad_idx <= reg["last_pad"]:
                        found = True

                        nth_pin = pad_idx - reg["first_pad"]
                        nth_bit = nth_pin * reg["bits_per_pin"]
                        
                        if pindata.bias_enable:
                            log_normal_parser(f"pad #{pad_idx} have bias enabled, prev reg is {hex(reg["value"])}, ")
                            data_mask = 1 << nth_bit
                            reg["value"] |= data_mask
                            bias_enabled = True
                        else:
                            log_normal_parser(f"pad #{pad_idx} have bias disabled, prev reg is {hex(reg["value"])}, ")
                            reg["value"] = zero_n_bits_at_ith_bit_of_32bits(reg["value"], reg["bits_per_pin"], nth_bit)
                        
                        log_normal_parser(f"after reg is {hex(reg["value"])}\n")

                if not found:
                    # This isn't necessarily an error, the pad's register could be reserved
                    # For example the HDMI's I2C bus's bias and drive strength registers are reserved.
                    log_warning_parser(f"cannot find the pin bank that the port {port} belongs in for biasing enable\n")

                # If bias is enabled, set the pull direction
                if bias_enabled:
                    found = False
                    for reg in pull_dir_registers:
                        if pad_idx >= reg["first_pad"] and pad_idx <= reg["last_pad"]:
                            found = True

                            nth_pin = pad_idx - reg["first_pad"]
                            nth_bit = nth_pin * reg["bits_per_pin"]
                            if pindata.bias_pullup:
                                log_normal_parser(f"pad #{pad_idx} have pull up, prev reg is {hex(reg["value"])}, ")
                                data_mask = 1 << nth_bit
                                reg["value"] |= data_mask
                            else:
                                log_normal_parser(f"pad #{pad_idx} have pull down, prev reg is {hex(reg["value"])}, ")
                                reg["value"] = zero_n_bits_at_ith_bit_of_32bits(reg["value"], reg["bits_per_pin"], nth_bit)
                        
                            log_normal_parser(f"after reg is {hex(reg["value"])}\n")
                
                    if not found:
                        # Also not an error for the reason above
                        log_warning_parser(f"cannot find the pin bank that the port {port} belongs in for bias direction\n")


                # Set drive strength if defined
                if pindata.drive_strength != -1:
                    ds_val = -1
                    if pindata.drive_strength == 500: # micro Amps
                        ds_val = 0
                    elif pindata.drive_strength == 2500:
                        ds_val = 1
                    elif pindata.drive_strength == 3000:
                        ds_val = 2
                    elif pindata.drive_strength == 4000:
                        ds_val = 3
                    else:
                        log_error_parser(f"unknown drive strength value of f{pindata.drive_strength} for pad #{pad_idx}\n")
                        exit(1) 
                    
                    found = False
                    for reg in ds_registers:
                        if pad_idx >= reg["first_pad"] and pad_idx <= reg["last_pad"]:
                            found = True

                            nth_pin = pad_idx - reg["first_pad"]
                            nth_bit = nth_pin * reg["bits_per_pin"]

                            # Fetch the bank value then zero out the bits that belong to this pad
                            zeroed_regval = zero_n_bits_at_ith_bit_of_32bits(reg["value"], reg["bits_per_pin"], nth_bit)
                            
                            # Prepare mux setting value to be OR'ed into the zeroed out slot
                            data_mask = ds_val << nth_bit

                            log_normal_parser(f"pad #{pad_idx} have drive strength {ds_val}, prev reg is {hex(reg["value"])}, ")

                            reg["value"] = zeroed_regval | data_mask

                            log_normal_parser(f"after reg is {hex(reg["value"])}\n")
                    if not found:
                        # Also not an error for the reason above
                        log_warning_parser(f"cannot find the pin bank that the port {port} belongs in for drive strength\n")

def consolidate_registers(mux_registers, ds_registers, bias_en_registers, pull_dir_registers) -> OrderedDict[int, int]:
    # key = offset to write, value = value to write to offset
    result = OrderedDict()
    for reg in mux_registers + ds_registers + bias_en_registers + pull_dir_registers:
        if reg["offset"] in result:
            log_normal_parser(f"consolidating existing register {hex(reg["offset"])}, old value is {hex(result[reg["offset"]])} with value {hex(reg["value"])}, result is {hex(result[reg["offset"]] | reg["value"])}")
            result[reg["offset"]] |= reg["value"]
        else:
            log_normal_parser(f"consolidating new register {hex(reg["offset"])} with value {hex(reg["value"])}")
            result[reg["offset"]] = reg["value"]

    return result

def register_values_to_assembler(out_dir: str, peripherals_data: OrderedDict[int, int], ao_data: OrderedDict[int, int]):
    with open(out_dir + "/pinctrl_config_data.s", "w") as file:
        file.write(".section .data\n")
        file.write("\t.align 4\n")

        file.write("\t.global num_peripheral_registers\n")
        file.write("\t.global peripheral_registers\n")

        file.write("\t.global num_ao_registers\n")
        file.write("\t.global ao_registers\n")

        file.write("\t.global pinmux_data_magic\n")

        file.write("num_peripheral_registers:\n")
        file.write(f"\t.word {len(peripherals_data)}\n")

        file.write("peripheral_registers:\n")
        for offset, value in peripherals_data.items():
            file.write("\t.word ")
            file.write(f"{int(offset)}, {int(value)}\n")

        file.write("num_ao_registers:\n")
        file.write(f"\t.word {len(ao_data)}\n")

        file.write("ao_registers:\n")
        for offset, value in ao_data.items():
            file.write("\t.word ")
            file.write(f"{int(offset)}, {int(value)}\n")

        file.write("pinmux_data_magic:\n")
        file.write(f"\t.word 1940637231\n")

##### MAIN

from odroidc4 import *

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
    
    is_dts_compatible(devicetree)

    enabled_phandles: dict[int, str] = fetch_enabled_devices(devicetree)
    log_normal_parser("Enabled devices found: " + str(enabled_phandles.values()))

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

    # Sanity check that all the enabled phandles have pinctrl data associated.
    processed_phandles: set[int] = set()
    for pindata in peripherals_dts_data:
        processed_phandles.add(pindata.phandle)
    for pindata in ao_dts_data:
        processed_phandles.add(pindata.phandle)
    if len(processed_phandles) != len(set(enabled_phandles.keys())):
        log_warning_parser(f"Seems like some phandles does not have pinctrl data associated: {set(enabled_phandles.keys()) - processed_phandles}")

    # Map pinmux data from DTS to memory values
    # Peripherals
    pindata_to_register_values(
        # Input
        peripherals_dts_data, function_to_group, pad_to_idx, port_to_pad, port_to_mux_func,
        # Output
        pinmux_registers, drive_strength_registers, bias_enable_registers, pull_up_registers
    )

    log_normal_parser("=================\n")

    # Always On
    pindata_to_register_values(
        # Input
        ao_dts_data, ao_function_to_group, ao_pad_to_idx, ao_port_to_pad, ao_port_to_mux_func,
        # Output
        ao_pinmux_registers, ao_drive_strength_registers, ao_bias_enable_registers, ao_pull_up_registers
    )

    # Collect data in easy to process format,
    # Also merges registers at the same offset
    peripherals_memory_data = consolidate_registers(pinmux_registers, drive_strength_registers, bias_enable_registers, pull_up_registers)
    log_normal_parser("=================\n")
    ao_memory_data = consolidate_registers(ao_pinmux_registers, ao_drive_strength_registers, ao_bias_enable_registers, ao_pull_up_registers)

    # Write to assembly file
    register_values_to_assembler(out_dir, peripherals_memory_data, ao_memory_data)

