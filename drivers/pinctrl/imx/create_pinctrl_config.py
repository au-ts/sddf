# Copyright 2024, UNSW
# SPDX-License-Identifier: BSD-2-Clause

import os
import sys
from devicetree import edtlib, dtlib
import struct

UINT32_T_SIZE = 4

def get_value_from_bytes_array(byte_array: bytes, index: int):
    "Extracts a 4-byte integer value from a 'bytes' array at a certain index"
    return int.from_bytes(byte_array[index*UINT32_T_SIZE : (index+1)* UINT32_T_SIZE], 'big', signed=False)

def get_pinctrl_info(device_nodes, enabled_phandles):

    # Our information dictionary will look like this
    return_dict = {
        'mux_reg': [],    # Offset of the mux register
        'conf_reg': [],   # Offset of pad configuration register
        'input_reg': [],  # Offset of select input register
        'mux_val': [],    # Mux value to be applied to `mux_reg`
        'input_val': [],  # Input value to be applied to `input_reg`
        'pad_setting': [] # Pad setting value to be applied to `conf_reg`
    }

    device: dtlib.Node
    for device in device_nodes.node_iter():
        pin_info = device.props.get('fsl,pins')
        if pin_info != None:
            # Check whether the device was enabled
            if device.props["phandle"].to_num() in enabled_phandles:
                print(f"pinmux group {device.name} is enabled")
            else:
                print(f"pinmux group {device.name} is disabled")
                continue

            # At this stage, we have the array of values
            # Since each device configuration comes in a set of six values, we'll loop through in sets of 6
            for i in range(len(pin_info.value) // (6 * UINT32_T_SIZE)):
                mux_reg = get_value_from_bytes_array(pin_info.value, 6*i)
                conf_reg = get_value_from_bytes_array(pin_info.value, 6*i+1)
                input_reg = get_value_from_bytes_array(pin_info.value, 6*i+2)
                mux_val = get_value_from_bytes_array(pin_info.value, 6*i+3)
                input_val = get_value_from_bytes_array(pin_info.value, 6*i+4)
                pad_setting = get_value_from_bytes_array(pin_info.value, 6*i+5)

                return_dict['mux_reg'].append(mux_reg)
                return_dict['conf_reg'].append(conf_reg)
                return_dict['input_reg'].append(input_reg)

                return_dict['mux_val'].append(mux_val)
                return_dict['input_val'].append(input_val)
                return_dict['pad_setting'].append(pad_setting)

    return return_dict


if __name__ == "__main__":

    if len(sys.argv) != 5:
        print("Usage: ")
        print("\tpython3 create_pinmux_setup.py <SoC-name> <dts-source> <pinmux-device-name> <output-dir>")
        exit(1)

    # Parse device tree file
    soc_name = sys.argv[1]
    devicetree = dtlib.DT(sys.argv[2], force=True)
    device_name = sys.argv[3]
    out_dir = sys.argv[4]

    # Check which devices are actually enabled
    enabled_phandles = set()
    node: dtlib.Node
    for node in devicetree.node_iter():
        if "status" in node.props.keys() and node.props["status"].to_string() == "okay":
            # Grab the pinctrl phandle, there's an issue though:
            # Some device, e.g. mmc@30b40000 of maaxboard for example
            # have multiple pinmux configuration it can be in:
            # default, 100mhz or 200mhz, right now we just grab the default state
            # This need to be revisited in the future if we work on an mmc driver for imx.
            if "pinctrl-0" in node.props.keys():
                for phandle in node.props["pinctrl-0"].to_nums():
                    print(f"device {node.name} is enabled")
                    enabled_phandles.add(phandle)

    # For the imx8mq, we have to locate the "pinctrl" device in the dts to be able to get our relevant info
    for node in devicetree.node_iter():
        if device_name in node.name:
            print(node.nodes)

            pinmux_dict = get_pinctrl_info(node, enabled_phandles)
            nums_pin_properties = len(pinmux_dict['mux_reg'])

            errored = False
            if len(set(pinmux_dict['mux_reg'])) != len(pinmux_dict['mux_reg']):
                print(f"there were duplicate mux registers!: offsets are {pinmux_dict['mux_reg']}")
                errored = True

            if len(set(pinmux_dict['conf_reg'])) != len(pinmux_dict['conf_reg']):
                print(f"there were duplicate config registers!, offsets are {pinmux_dict['conf_reg']}")
                errored = True

            # There can be multiple zero offsets where the input settings are not defined
            santised_input_regs = [reg for reg in pinmux_dict['input_reg'] if reg != 0]
            if len(set(santised_input_regs)) != len(santised_input_regs):
                print(f"there were duplicate input registers!, offsets are {pinmux_dict['input_reg']}")
                errored = True

            if errored:
                exit(1)

            with open(out_dir + "/pinctrl_config_data.S", "w") as file:
                file.write(".data\n")

                file.write("\t.align 4\n")
                file.write("\t.global num_iomuxc_configs\n")
                file.write("\t.global iomuxc_configs\n")

                file.write("num_iomuxc_configs:\n")
                file.write(f"\t.word {nums_pin_properties}\n")

                file.write("iomuxc_configs:\n")
                for i in range(0, nums_pin_properties):
                    file.write("\t.word ")
                    file.write(f"{pinmux_dict['mux_reg'][i]}, {pinmux_dict['conf_reg'][i]}, {pinmux_dict['input_reg'][i]}, {pinmux_dict['mux_val'][i]}, {pinmux_dict['input_val'][i]}, {pinmux_dict['pad_setting'][i]}\n")

            break