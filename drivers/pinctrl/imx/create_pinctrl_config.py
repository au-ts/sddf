# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause

import sys
from devicetree import dtlib

# Compatible boards and the path of its pinmux device in the device tree.
compatible_board_to_pinctrl_dev_path = {
    "fsl,imx8mm-evk": "/soc@0/bus@30000000/pinctrl@30330000",
    "fsl,imx8mq-evk": "/soc@0/bus@30000000/pinctrl@30330000",
    "avnet/embest,maaxboard": "/soc@0/bus@30000000/iomuxc@30330000",
    "fsl,imx8mp-evk": "/soc@0/bus@30000000/pinctrl@30330000",
}

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

    if len(sys.argv) != 3:
        print("Usage: ")
        print("\tpython3 create_pinmux_setup.py <dts-source> <output-dir>")
        exit(1)

    # Parse device tree file
    devicetree = dtlib.DT(sys.argv[1], force=True)
    out_dir = sys.argv[2]

    # Ensure compatibility
    target_compats = devicetree.get_node("/").props.get('compatible').to_strings()
    matched_compat_str = None
    for target_compat in target_compats:
        if target_compat in compatible_board_to_pinctrl_dev_path.keys():
            matched_compat_str = target_compat
            break
    if matched_compat_str is None:
        print(f'Your target board {target_compats} isn\'t compatible with this driver.')
        sys.exit(1)

    # Check which devices are actually enabled
    enabled_phandles = set()
    node: dtlib.Node
    for node in devicetree.node_iter():
        if "status" in node.props.keys() and node.props["status"].to_string() == "okay":
            # Grab the pinctrl phandle, there's an issue though:
            # Some device, e.g. mmc@30b40000 of maaxboard for example
            # have multiple pinmux configuration it can be in:
            # default, 100mhz or 200mhz, right now we just grab the default state.
            if "pinctrl-0" in node.props.keys():
                for phandle in node.props["pinctrl-0"].to_nums():
                    print(f"device {node.name} is enabled")
                    enabled_phandles.add(phandle)

    # Now we locate the pinctrl device to pull the configuration data.
    pinctrl_node = devicetree.get_node(compatible_board_to_pinctrl_dev_path[matched_compat_str])
    pinmux_dict = get_pinctrl_info(pinctrl_node, enabled_phandles)
    nums_pin_properties = len(pinmux_dict['mux_reg'])

    errored = False
    # This can happen on incorrectly encoded device trees where 1 register is specified twice.
    if len(set(pinmux_dict['mux_reg'])) != len(pinmux_dict['mux_reg']):
        print(f"there were duplicate mux registers!: offsets are {[hex(n) for n in sorted(pinmux_dict['mux_reg'])]}")
        errored = True

    if len(set(pinmux_dict['conf_reg'])) != len(pinmux_dict['conf_reg']):
        print(f"there were duplicate config registers!, offsets are {[hex(n) for n in sorted(pinmux_dict['conf_reg'])]}")
        errored = True

    # There can be multiple zero offsets where the input settings are not defined
    santised_input_regs = [reg for reg in pinmux_dict['input_reg'] if reg != 0]
    if len(set(santised_input_regs)) != len(santised_input_regs):
        print(f"there were duplicate input registers!, offsets are {pinmux_dict['input_reg']}")
        errored = True

    if errored:
        exit(1)

    print(f"writing pinctrl config data to {out_dir + '/pinctrl_config_data.s'}")
    with open(out_dir + "/pinctrl_config_data.s", "w") as file:
        file.write(".section .data\n")

        file.write("\t.align 4\n")
        file.write("\t.global num_iomuxc_configs\n")
        file.write("\t.global iomuxc_configs\n")

        file.write("num_iomuxc_configs:\n")
        file.write(f"\t.word {nums_pin_properties}\n")

        file.write("iomuxc_configs:\n")
        for i in range(0, nums_pin_properties):
            file.write("\t.word ")
            file.write(f"{pinmux_dict['mux_reg'][i]}, {pinmux_dict['conf_reg'][i]}, {pinmux_dict['input_reg'][i]}, {pinmux_dict['mux_val'][i]}, {pinmux_dict['input_val'][i]}, {pinmux_dict['pad_setting'][i]}\n")
