# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause

import sys
from devicetree import dtlib

# Document referenced:
# [1] Linux: Documentation/devicetree/bindings/pinctrl/fsl,imx-pinctrl.txt
# [2] Linux: Documentation/devicetree/bindings/pinctrl/fsl,imx8mm-pinctrl.yaml
# [3] Linux: drivers/pinctrl/freescale/pinctrl-imx.c

# [1]
# Software Input On Field.
# Force the selected mux mode input path no matter of MUX_MODE functionality.
# By default the input path is determined by functionality of the selected
# mux mode (regular). This bit will be set in "pad_setting"
PAD_SION = 1 << 30
# If the above bit is set, clear it from "pad_setting" then set this bit in "mux_reg"
MUX_SION = 1 << 4

# Compatible boards and the path of its pinmux device in the device tree.
compatible_board_to_pinctrl_dev_path: dict[str, str] = {
    "fsl,imx8mm-evk": "/soc@0/bus@30000000/pinctrl@30330000",
    "fsl,imx8mq-evk": "/soc@0/bus@30000000/pinctrl@30330000",
    "avnet/embest,maaxboard": "/soc@0/bus@30000000/iomuxc@30330000",
    "fsl,imx8mp-evk": "/soc@0/bus@30000000/pinctrl@30330000",
}

UINT32_T_SIZE = 4
PINCTRL_CONFIG_DATA_MAGIC = "0x696D70696E6D7578"  # "impinmux"


class PinctrlRegisterData:
    def __init__(
        self,
        mux_reg: int,
        conf_reg: int,
        input_reg: int,
        mux_val: int,
        input_val: int,
        pad_setting: int,
    ):
        self.mux_reg = mux_reg
        self.conf_reg = conf_reg
        self.input_reg = input_reg
        self.mux_val = mux_val
        self.input_val = input_val
        self.pad_setting = pad_setting

    def __str__(self):
        return f"mux reg @ {hex(self.mux_reg)} = {hex(self.mux_val)}, conf reg @ {hex(self.conf_reg)} = {hex(self.pad_setting)}, input reg @ {hex(self.input_reg)} = {hex(self.input_val)}"


class PinctrlStateData:
    # Represent a singular pinctrl state of a device.

    def __init__(
        self,
        name: str,
        index: int,
        group_names: list[str],
        phandles: list[int],
        registers: list[PinctrlRegisterData],
    ):
        self.name = name
        self.index = index
        self.group_names = group_names
        self.phandles = phandles
        self.registers = registers

    def __str__(self):
        serialised = f"* Config source name `{self.name}` at index {self.index} with group name `{str(self.group_names)}` and phandles {str(self.phandles)} have registers:\n"
        for reg in self.registers:
            serialised += str(reg) + "\n"
        return serialised


class PinctrlClientDeviceData:
    # Represent a device that requires pinctrl configuration. For example, `mmc@30b40000` in maaxboard.dts.

    def __init__(
        self,
        aliases_node: dtlib.Node,
        pinctrl_node: dtlib.Node,
        client_device_node: dtlib.Node,
    ):
        self.client_device_node: dtlib.Node = client_device_node
        # A device can have multiple different pin states it selects from at runtime.
        # Though all devices that require pinctrl have a "default" config.
        self.pinctrl_configs: list[PinctrlStateData] = []
        self.alias: str = "<none>"

        # Check and record whether this device have an alias
        for alias_name in aliases_node.props:
            if (
                aliases_node.props.get(alias_name).to_string()
                == client_device_node.path
            ):
                self.alias = alias_name
                break

        # Make sure the given device have a need for pinctrl configuration
        assert "status" in client_device_node.props.keys()
        assert client_device_node.props["status"].to_string() == "okay"
        assert "pinctrl-0" in client_device_node.props.keys()

        # Grab and parse all the possible pin configurations of this device.
        for config_idx, config_name in enumerate(
            client_device_node.props.get("pinctrl-names").to_strings()
        ):
            target_prop: str = f"pinctrl-{config_idx}"
            target_phandles: list[int] = client_device_node.props.get(
                target_prop
            ).to_nums()

            config_data = get_pinctrl_info(
                pinctrl_node, target_phandles, config_name, config_idx
            )
            assert config_data is not None
            self.pinctrl_configs.append(config_data)

    def __str__(self):
        serialised = f"** Device `{self.client_device_node.path}` with alias {self.alias} have the following pinctrl configs:\n"
        for config in self.pinctrl_configs:
            serialised += str(config) + "\n"
        return serialised


class AssemblyDataLabelAllocator:
    def __init__(self, label_prefix: str):
        self.watermark: int = -1
        self.label_prefix: str = label_prefix

    def create_label(self) -> str:
        self.watermark += 1
        return self.label_prefix + str(self.watermark)


class AssemblyStringAllocator:
    # A simple class to manage the allocation of strings in the pinctrl data assembly file.
    def __init__(self, label_prefix: str):
        self.label_allocator = AssemblyDataLabelAllocator(label_prefix)
        # string -> label
        self.allocated_strings: dict[str, str] = {}

    # Returns a label to the target string
    def create_label_for_str(self, target: str) -> str:
        if target not in self.allocated_strings:
            self.allocated_strings[target] = self.label_allocator.create_label()
        return self.allocated_strings[target]

    def to_assembler(self) -> str:
        asm_strs = ""
        for string in self.allocated_strings:
            asm_strs += f'{self.allocated_strings[string]}: .asciz "{string}"\n'
        return asm_strs


class AssemblyDataObject:
    def __init__(self, label: str):
        self.data = f"{label}:\n"

    def add_word(self, value):
        self.data += f"\t.word {str(value)}\n"

    def add_quad(self, value):
        self.data += f"\t.quad {str(value)}\n"

    def add_ptr_from_label(self, label: str):
        self.data += f"\t.quad {label}\n"

    def to_assembler(self) -> str:
        return self.data + "\n"


class PinctrlData:
    def __init__(self):
        self.devices_with_pinctrl: list[PinctrlClientDeviceData] = []

    def __str__(self):
        serialised = ""
        for dev in self.devices_with_pinctrl:
            serialised += str(dev)
        return serialised

    def parse(self, dt: dtlib.DT, pinctrl_dev_path: str):
        pinctrl_node = dt.get_node(
            pinctrl_dev_path
        )  # This is the `iomuxc@30330000` node
        aliases_node = dt.get_node("/aliases")
        # Find all devices that need pinctrl configuration
        device_node: dtlib.Node
        for device_node in devicetree.node_iter():
            if (
                "status" in device_node.props.keys()
                and device_node.props["status"].to_string() == "okay"
            ):
                if "pinctrl-names" in device_node.props.keys():
                    self.devices_with_pinctrl.append(
                        PinctrlClientDeviceData(aliases_node, pinctrl_node, device_node)
                    )

    def write_assembler(self, out_dir: str):
        # Gather all the data we need for the assembly
        num_devices = 0

        # Manage allocation of strings and their labels in the assembly file to prevent duplication
        str_asm_allocator = AssemblyStringAllocator("pinctrl_config_str_")

        label_pin_regs_array_allocator = AssemblyDataLabelAllocator(
            "pinctrl_config_pins_reg_"
        )
        asm_pin_regs: list[AssemblyDataObject] = []

        label_state_object_allocator = AssemblyDataLabelAllocator(
            "pinctrl_config_state_obj_"
        )
        asm_states: list[AssemblyDataObject] = []

        label_states_array_allocator = AssemblyDataLabelAllocator(
            "pinctrl_config_states_"
        )
        asm_states_arrays: list[AssemblyDataObject] = []

        asm_devices = AssemblyDataObject("pinctrl_client_devices_configs")

        # For every device requiring pinctrl config, write their `pinctrl_client_device_data_t` C struct
        for device in self.devices_with_pinctrl:
            # For every pinctrl state of this device, write its `pinctrl_client_device_state_t` C struct
            this_device_pinctrl_states_labels: list[str] = []
            for state in device.pinctrl_configs:
                # For every pin in this state, write its `pinctrl_pin_register_t` C struct
                state_pins_label = label_pin_regs_array_allocator.create_label()
                asm_pin_regs.append(AssemblyDataObject(state_pins_label))

                num_pins = 0
                for pin in state.registers:
                    asm_pin_regs[-1].add_word(pin.mux_reg)
                    asm_pin_regs[-1].add_word(pin.conf_reg)
                    asm_pin_regs[-1].add_word(pin.input_reg)
                    asm_pin_regs[-1].add_word(pin.mux_val)
                    asm_pin_regs[-1].add_word(pin.input_val)
                    asm_pin_regs[-1].add_word(pin.pad_setting)
                    num_pins += 1

                # Now that we have the label to all the pins in this state, create the `pinctrl_client_device_state_t`
                state_label = label_state_object_allocator.create_label()
                asm_states.append(AssemblyDataObject(state_label))
                asm_states[-1].add_ptr_from_label(
                    str_asm_allocator.create_label_for_str(state.name)
                )
                asm_states[-1].add_word(num_pins)
                asm_states[-1].add_ptr_from_label(state_pins_label)

                this_device_pinctrl_states_labels.append(state_label)

            # We've encoded all the states and have their labels, create a states array (the `**state`)
            states_array_label = label_states_array_allocator.create_label()
            asm_states_arrays.append(AssemblyDataObject(states_array_label))
            for state_label in this_device_pinctrl_states_labels:
                asm_states_arrays[-1].add_ptr_from_label(state_label)

            # Finally create the `pinctrl_client_device_data`
            asm_devices.add_ptr_from_label(
                str_asm_allocator.create_label_for_str(device.client_device_node.path)
            )
            if device.alias is not None:
                asm_devices.add_ptr_from_label(
                    str_asm_allocator.create_label_for_str(device.alias)
                )
            else:
                asm_devices.add_ptr_from_label(
                    str_asm_allocator.create_label_for_str("")
                )
            asm_devices.add_word(len(this_device_pinctrl_states_labels))
            asm_devices.add_ptr_from_label(states_array_label)

            num_devices += 1

        # Write all the data to .s file
        with open(out_dir + "/pinctrl_config_data.s", "w") as file:
            file.write(".section .rodata\n")

            file.write("\t.align 4\n")
            file.write("\t.global pinctrl_config_data_magic\n")
            file.write("\t.global pinctrl_client_devices_configs\n")
            file.write("\t.global num_pinctrl_client_devices_configs\n")

            file.write(
                f"pinctrl_config_data_magic:\n\t.quad {PINCTRL_CONFIG_DATA_MAGIC}\n"
            )
            file.write(f"num_pinctrl_client_devices_configs:\n\t.word {num_devices}\n")

            file.write(asm_devices.to_assembler())
            file.write(str_asm_allocator.to_assembler())

            [file.write(asm_pin_reg.to_assembler()) for asm_pin_reg in asm_pin_regs]
            [file.write(asm_state.to_assembler()) for asm_state in asm_states]
            [
                file.write(asm_states_array.to_assembler())
                for asm_states_array in asm_states_arrays
            ]


def get_value_from_bytes_array(byte_array: bytes, index: int) -> int:
    # Extracts a 4-byte integer value from a 'bytes' array at a certain index
    return int.from_bytes(
        byte_array[index * UINT32_T_SIZE : (index + 1) * UINT32_T_SIZE],
        "big",
        signed=False,
    )


def get_pinctrl_info(
    pinctrl_device: dtlib.Node,
    target_pinctrl_config_phandles: list[int],
    target_pinctrl_config_name: str,
    target_pinctrl_config_index: int,
) -> PinctrlStateData:
    # pinctrl_device is the DT node to the pinctrl device that have all the configuration values.
    # And pinctrl_config_phandle is the phandle to the specific group inside pinctrl_device

    group_names: list[str] = []
    phandles: list[int] = []
    regs: list[PinctrlRegisterData] = []

    for pinctrl_config_node in pinctrl_device.node_iter():
        pinctrl_config_node_data = pinctrl_config_node.props.get("fsl,pins")
        if pinctrl_config_node_data != None:
            pinctrl_config_node_phandle = pinctrl_config_node.props.get(
                "phandle"
            ).to_num()
            if pinctrl_config_node_phandle in target_pinctrl_config_phandles:
                # We only support the normal configuration, not the SCU configuration.
                assert len(pinctrl_config_node_data.value) % 6 == 0

                group_names.append(pinctrl_config_node.name)
                phandles.append(pinctrl_config_node_phandle)

                # [2]
                # At this stage, we have the array of values
                # Since each device configuration comes in a set of six values, we'll loop through in sets of 6
                for i in range(
                    len(pinctrl_config_node_data.value) // (6 * UINT32_T_SIZE)
                ):
                    mux_reg = get_value_from_bytes_array(
                        pinctrl_config_node_data.value, 6 * i
                    )
                    conf_reg = get_value_from_bytes_array(
                        pinctrl_config_node_data.value, 6 * i + 1
                    )
                    input_reg = get_value_from_bytes_array(
                        pinctrl_config_node_data.value, 6 * i + 2
                    )
                    mux_val = get_value_from_bytes_array(
                        pinctrl_config_node_data.value, 6 * i + 3
                    )
                    input_val = get_value_from_bytes_array(
                        pinctrl_config_node_data.value, 6 * i + 4
                    )
                    pad_setting = get_value_from_bytes_array(
                        pinctrl_config_node_data.value, 6 * i + 5
                    )

                    # [3]: checkout tag v6.1 at line 557
                    # For pins that have SION bit set in "pad_setting", set it in "mux_val" and clear it from "pad_setting"
                    if pad_setting & PAD_SION:
                        mux_val |= MUX_SION
                        pad_setting &= ~PAD_SION

                    regs.append(
                        PinctrlRegisterData(
                            mux_reg,
                            conf_reg,
                            input_reg,
                            mux_val,
                            input_val,
                            pad_setting,
                        )
                    )

    if len(regs) > 0:
        return PinctrlStateData(
            target_pinctrl_config_name,
            target_pinctrl_config_index,
            group_names,
            phandles,
            regs,
        )
    else:
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
    target_compats = devicetree.get_node("/").props.get("compatible").to_strings()
    matched_compat_str = None
    for target_compat in target_compats:
        if target_compat in compatible_board_to_pinctrl_dev_path.keys():
            matched_compat_str = target_compat
            break
    if matched_compat_str is None:
        print(f"Your target board {target_compats} isn't compatible with this driver.")
        sys.exit(1)

    # Start parsing
    pinctrl_data = PinctrlData()
    pinctrl_data.parse(
        devicetree, compatible_board_to_pinctrl_dev_path[matched_compat_str]
    )
    print(pinctrl_data)

    pinctrl_data.write_assembler(out_dir)
