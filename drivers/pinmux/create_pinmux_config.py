import os
import sys
from devicetree import edtlib, dtlib
import struct

PINMUX_MAX = 1000
UINT32_T_SIZE = 4

def get_value_from_bytes_array(byte_array: bytes, index: int):
    "Extracts a 4-byte integer value from a 'bytes' array at a certain index"
    return int.from_bytes(byte_array[index*UINT32_T_SIZE : (index+1)* UINT32_T_SIZE], 'big', signed=False)

def get_imx8mm_pinctrl_info(device_nodes):

    # Our information dictionary will look like this

    return_dict = {
        'mux_reg': [],
        'conf_reg': [],
        'input_reg': [],
        'mux_val': [],
        'input_val': [],
        'pad_setting': []

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

    if len(sys.argv) != 3:
        print("Usage: ")
        print("\tpython3 create_pinmux_setup.py <dts-source> <output-dir>")
        exit(1)
    
    # Parse device tree file
    devicetree = dtlib.DT(sys.argv[1], force=True)

    # For the imx8mm-evk, we have to locate the "pinctrl" device in the dts to be able to get our relevant info
    for node in devicetree.node_iter():
        if "pinctrl" in node.name:
            pinmux_dict = get_imx8mm_pinctrl_info(node.nodes['imx8mm-evk'])
                

            # This is an interesting way of writing my dict values to an assembly file
            # It works so I won't bother changing it right now
            with open(sys.argv[2]+"/pinmux_config_data.s", "w") as file:
                file.write("\t.section .data\n")
                file.write("\t.global conf\n")
                file.write("conf:\n")
                file.write(f"\t.word {str(len(pinmux_dict['mux_reg']))}\n")
                
                for val_arr in pinmux_dict.values():
                    file.write("\t.word ")
                    for val in val_arr[:-1]:
                        file.write(f'{str(val)}, ')
                    file.write(f'{str(val_arr[-1])}\n')
                    file.write(f'\t.skip {str((PINMUX_MAX - len(val_arr))*UINT32_T_SIZE)}\n')

    