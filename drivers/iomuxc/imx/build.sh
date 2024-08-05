rm -rf build/* && \

aarch64-none-elf-gcc -c -mstrict-align -ffreestanding -mcpu=cortex-a53 -I/Users/dreamliner787-9/microkit-sdk-1.3.0/board/maaxboard/debug/include -I../../../include/ ../../../util/printf.c -o build/printf.o && \

python3 create_iomuxc_config.py dts/maaxboard.dts build && \
aarch64-none-elf-as build/pinmux_config_data.s -o build/pinmux_config_data.o && \
aarch64-none-elf-gcc -c -mstrict-align -ffreestanding -mcpu=cortex-a53 -I/Users/dreamliner787-9/microkit-sdk-1.3.0/board/maaxboard/debug/include -I../../../include/ driver.c -o build/driver.o && \
aarch64-none-elf-ld -L/Users/dreamliner787-9/microkit-sdk-1.3.0/board/maaxboard/debug/lib -lmicrokit -Tmicrokit.ld build/driver.o build/pinmux_config_data.o build/printf.o -o build/iomuxc_driver.elf && \
/Users/dreamliner787-9/microkit-sdk-1.3.0/bin/microkit iomuxc.system --search-path build --board maaxboard --config debug -o build/sel4-image && \
# scp build/sel4-image billn@tftp:/tftpboot/maaxboard_billn/sel4-image

mq.sh run -s maaxboard2 -f build/sel4-image -c "ABCXYZ"
 