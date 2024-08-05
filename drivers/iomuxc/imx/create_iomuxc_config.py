import os
import sys
from devicetree import edtlib, dtlib
import struct

UINT32_T_SIZE = 4

def get_value_from_bytes_array(byte_array: bytes, index: int):
    "Extracts a 4-byte integer value from a 'bytes' array at a certain index"
    return int.from_bytes(byte_array[index*UINT32_T_SIZE : (index+1)* UINT32_T_SIZE], 'big', signed=False)

def get_imx8mm_pinctrl_info(device_nodes):

    # Our information dictionary will look like this
    return_dict = {
        'mux_reg': [],    # Offset of the mux register
        'conf_reg': [],   # Offset of pad configuration register
        'input_reg': [],  # Offset of select input register
        'mux_val': [],    # Mux value to be applied to `mux_reg`
        'input_val': [],  # Input value to be applied to `input_reg`
        'pad_setting': [] # Pad setting value to be applied to `conf_reg`
    }

    for device in device_nodes.node_iter():
        pin_info = device.props.get('fsl,pins')
        if pin_info != None:
            # At this stage, we have the array of values
            # Since each device configuration comes in a set of six values, we'll loop through in sets of 6
            for i in range(len(pin_info.value)//(6*UINT32_T_SIZE)):
                return_dict['mux_reg'].append(get_value_from_bytes_array(pin_info.value, 6*i))
                return_dict['conf_reg'].append(get_value_from_bytes_array(pin_info.value, 6*i+1))
                return_dict['input_reg'].append(get_value_from_bytes_array(pin_info.value, 6*i+2))
                return_dict['mux_val'].append(get_value_from_bytes_array(pin_info.value, 6*i+3))
                return_dict['input_val'].append(get_value_from_bytes_array(pin_info.value, 6*i+4))
                return_dict['pad_setting'].append(get_value_from_bytes_array(pin_info.value, 6*i+5))

    return return_dict


if __name__ == "__main__":

    if len(sys.argv) != 4:
        print("Usage: ")
        print("\tpython3 create_pinmux_setup.py <SoC-name> <dts-source> <output-dir>")
        exit(1)
    
    # Parse device tree file
    soc_name = sys.argv[1]
    devicetree = dtlib.DT(sys.argv[2], force=True)
    out_dir = sys.argv[3]

    # For the imx8mm-evk, we have to locate the "pinctrl" device in the dts to be able to get our relevant info
    for node in devicetree.node_iter():
        if "iomuxc" in node.name:
            pinmux_dict = get_imx8mm_pinctrl_info(node.nodes[soc_name])
            nums_pin_properties = len(pinmux_dict['mux_reg'])

            # This is an interesting way of writing my dict values to an assembly file
            # It works so I won't bother changing it right now
            with open(out_dir + "/pinmux_config_data.s", "w") as file:
                file.write("\t.section .data\n")

                file.write("\t.global num_iomuxc_configs\n")
                file.write("\t.global iomuxc_configs\n")

                file.write("num_iomuxc_configs:\n")
                file.write(f"\t.word {nums_pin_properties}\n")

                file.write("iomuxc_configs:\n")
                for i in range(0, nums_pin_properties):
                    file.write("\t.word ")
                    file.write(f"{pinmux_dict['mux_reg'][i]}, {pinmux_dict['conf_reg'][i]}, {pinmux_dict['input_reg'][i]}, {pinmux_dict['mux_val'][i]}, {pinmux_dict['input_val'][i]}, {pinmux_dict['pad_setting'][i]}\n")
            
            break


    