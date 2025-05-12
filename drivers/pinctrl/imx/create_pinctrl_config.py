# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause

import sys
from devicetree import dtlib

# From Linux's Documentation/devicetree/bindings/pinctrl/fsl,imx-pinctrl.txt
# Special values for pad_setting:
# Indicate this pin does not need config
NO_PAD_CTL = (1 << 31)
# Software Input On Field.
# Force the selected mux mode input path no matter of MUX_MODE functionality.
# By default the input path is determined by functionality of the selected
# mux mode (regular). This bit will be set in "pad_setting"
PAD_SION = (1 << 30)
# If the above bit is set, clear it from "pad_setting" then set this bit in "mux_reg"
MUX_SION = (1 << 4)

# Compatible boards and the path of its pinmux device in the device tree.
compatible_board_to_pinctrl_dev_path: dict[str, str] = {
    "fsl,imx8mm-evk": "/soc@0/bus@30000000/pinctrl@30330000",
    "fsl,imx8mq-evk": "/soc@0/bus@30000000/pinctrl@30330000",
    "avnet/embest,maaxboard": "/soc@0/bus@30000000/iomuxc@30330000",
    "fsl,imx8mp-evk": "/soc@0/bus@30000000/pinctrl@30330000",
}

UINT32_T_SIZE = 4

class PinctrlRegisterData:
    def __init__(self, mux_reg: int, conf_reg: int, input_reg: int, mux_val: int, input_val: int, pad_setting: int):
        self.mux_reg = mux_reg
        self.conf_reg = conf_reg
        self.input_reg = input_reg
        self.mux_val = mux_val
        self.input_val = input_val
        self.pad_setting = pad_setting

    def __str__(self):
        return f"mux reg @ {hex(self.mux_reg)} = {hex(self.mux_val)}, conf reg @ {hex(self.conf_reg)} = {hex(self.pad_setting)}, input reg @ {hex(self.input_reg)} = {hex(self.input_val)}"

class PinctrlConfigData:
    # Represent a singular pinctrl configuration of a device.

    def __init__(self, name: str, config_node: dtlib.Node, registers: list[PinctrlRegisterData]):
        self.name = name
        self.config_node = config_node
        self.registers = registers

    def __str__(self):
        serialised = f"* Config source name `{self.name}` with group name `{self.config_node.name}` and phandle {hex(self.config_node.props.get("phandle").to_num())} have registers:\n"
        for reg in self.registers:
            serialised += str(reg) + "\n"
        return serialised

class PinctrlDeviceData:
    # Represent a device that requires pinctrl configuration. For example, `mmc@30b40000` in maaxboard.dts.

    def __init__(self, pinctrl_node: dtlib.Node, device_node: dtlib.Node):
        self.device_node: dtlib.Node = device_node
        # A device can have multiple different pin configurations it select from at runtime.
        # Though all devices that require pinctrl have a "default" config.
        self.pinctrl_configs: list[PinctrlConfigData] = []
    
        # Make sure the given device have a need for pinctrl configuration
        assert "status" in device_node.props.keys()
        assert device_node.props["status"].to_string() == "okay"
        assert "pinctrl-0" in device_node.props.keys()
        
        # Grab and parse all the possible pin configurations of this device.
        for config_idx, config_name in enumerate(device_node.props.get("pinctrl-names").to_strings()):
            target_prop: str = f"pinctrl-{config_idx}"
            target_phandle: int = device_node.props.get(target_prop).to_num()

            config_data = get_pinctrl_info(pinctrl_node, target_phandle, config_name)
            assert config_data is not None
            self.pinctrl_configs.append(config_data)

    def __str__(self):
        serialised = f"** Device `{self.device_node.path}` have the following pinctrl configs:\n"
        for config in self.pinctrl_configs:
            serialised += str(config) + "\n"
        return serialised


class PinctrlData:
    def __init__(self):
        self.devices_with_pinctrl: list[PinctrlDeviceData] = []

    def __str__(self):
        serialised = ""
        for dev in self.devices_with_pinctrl:
            serialised += str(dev)
        return serialised
    
    def parse(self, dt: dtlib.DT, pinctrl_dev_path: str):
        pinctrl_node = dt.get_node(pinctrl_dev_path) # This is `iomuxc@30330000`
        # Find all devices that need pinctrl configuration
        device_node: dtlib.Node
        for device_node in devicetree.node_iter():
            if "status" in device_node.props.keys() and device_node.props["status"].to_string() == "okay":
                if "pinctrl-names" in device_node.props.keys():
                    self.devices_with_pinctrl.append(PinctrlDeviceData(pinctrl_node, device_node))
    
    def to_assembler(self, out_dir: str):
        # Gather all the data we need for the assembly
        num_pins = 0

        # There will two parts, the first part contains all the `iomuxc_config_t`
        # and the second contains all the strings referenced by the first part.
        iomuxc_configs = "iomuxc_configs:\n"
        strings_def = "pinctrl_str_conf_name_default: .asciz \"default\"\n"
        string_label_counter = 0

        for device in self.devices_with_pinctrl:
            for config in device.pinctrl_configs:
                for reg in config.registers:
                    num_pins += 1
                    # Write the numbers first
                    iomuxc_configs += f"\t.word {str(reg.mux_reg)}, {str(reg.conf_reg)}, {str(reg.input_reg)}, {str(reg.mux_val)}, {str(reg.input_val)}, {str(reg.pad_setting)}, {str(config.config_node.props.get("phandle").to_num())}\n"

                    # Take care of string data, first define the string, the reference them
                    # Device path:
                    str_label = f"pinctrl_str_{string_label_counter}"
                    strings_def += f"{str_label}: .asciz \"{device.device_node.path}\"\n"
                    iomuxc_configs += f"\t.quad {str_label}, "
                    string_label_counter += 1

                    # Config name:
                    str_label = f"pinctrl_str_{string_label_counter}"
                    strings_def += f"{str_label}: .asciz \"{config.name}\"\n"
                    iomuxc_configs += f"{str_label}, "
                    string_label_counter += 1

                    # Group name:
                    str_label = f"pinctrl_str_{string_label_counter}"
                    strings_def += f"{str_label}: .asciz \"{config.config_node.name}\"\n"
                    iomuxc_configs += f"{str_label}\n"
                    string_label_counter += 1

        with open(out_dir + "/pinctrl_config_data.s", "w") as file:
            file.write(".section .rodata\n")

            file.write("\t.align 4\n")
            file.write("\t.global num_iomuxc_configs\n")
            file.write("\t.global iomuxc_configs\n")

            file.write("num_iomuxc_configs:\n")
            file.write(f"\t.word {num_pins}\n")

            file.write(iomuxc_configs)
            file.write(strings_def)

def get_value_from_bytes_array(byte_array: bytes, index: int) -> int:
    # Extracts a 4-byte integer value from a 'bytes' array at a certain index
    return int.from_bytes(byte_array[index*UINT32_T_SIZE: (index+1) * UINT32_T_SIZE], 'big', signed=False)


def get_pinctrl_info(pinctrl_device: dtlib.Node, target_pinctrl_config_phandle: int, target_pinctrl_config_name: str) -> PinctrlConfigData:
    # pinctrl_device is the DT node to the pinctrl device that have all the configuration values.
    # And pinctrl_config_phandle is the phandle to the specific group inside pinctrl_device

    for pinctrl_config_node in pinctrl_device.node_iter():
        pinctrl_config_node_data = pinctrl_config_node.props.get('fsl,pins')
        if pinctrl_config_node_data != None:
            pinctrl_config_node_phandle = pinctrl_config_node.props.get("phandle").to_num()
            if pinctrl_config_node_phandle == target_pinctrl_config_phandle:
                # We only support the normal configuration, not the SCU configuration.
                assert len(pinctrl_config_node_data.value) % 6 == 0

                regs: list[PinctrlRegisterData] = []

                # At this stage, we have the array of values
                # Since each device configuration comes in a set of six values, we'll loop through in sets of 6
                for i in range(len(pinctrl_config_node_data.value) // (6 * UINT32_T_SIZE)):
                    mux_reg = get_value_from_bytes_array(pinctrl_config_node_data.value, 6*i)
                    conf_reg = get_value_from_bytes_array(pinctrl_config_node_data.value, 6*i+1)
                    input_reg = get_value_from_bytes_array(pinctrl_config_node_data.value, 6*i+2)
                    mux_val = get_value_from_bytes_array(pinctrl_config_node_data.value, 6*i+3)
                    input_val = get_value_from_bytes_array(pinctrl_config_node_data.value, 6*i+4)
                    pad_setting = get_value_from_bytes_array(pinctrl_config_node_data.value, 6*i+5)

                    # For pins that have SION bit set in "pad_setting", set it in "mux_val" and clear it from "pad_setting"
                    if pad_setting & PAD_SION:
                        mux_val |= MUX_SION
                        pad_setting &= ~PAD_SION

                    regs.append(PinctrlRegisterData(mux_reg, conf_reg, input_reg, mux_val, input_val, pad_setting))
                
                return PinctrlConfigData(target_pinctrl_config_name, pinctrl_config_node, regs)

    return None

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

    # Start parsing
    pinctrl_data = PinctrlData()
    pinctrl_data.parse(devicetree, compatible_board_to_pinctrl_dev_path[matched_compat_str])
    print(pinctrl_data)

    pinctrl_data.to_assembler(out_dir)

    # nums_pin_properties = len(pinmux_dict['mux_reg'])
    # print(f"writing pinctrl config data to {out_dir + '/pinctrl_config_data.s'}")
    # with open(out_dir + "/pinctrl_config_data.s", "w") as file:
    #     file.write(".section .data\n")

    #     file.write("\t.align 4\n")
    #     file.write("\t.global num_iomuxc_configs\n")
    #     file.write("\t.global iomuxc_configs\n")

    #     file.write("num_iomuxc_configs:\n")
    #     file.write(f"\t.word {nums_pin_properties}\n")

    #     file.write("iomuxc_configs:\n")
    #     for i in range(0, nums_pin_properties):
    #         file.write("\t.word ")
    #         file.write(
    #             f"{pinmux_dict['mux_reg'][i]}, {pinmux_dict['conf_reg'][i]}, {pinmux_dict['input_reg'][i]}, {pinmux_dict['mux_val'][i]}, {pinmux_dict['input_val'][i]}, {pinmux_dict['pad_setting'][i]}\n")
