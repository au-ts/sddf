rm -rf build/* && \


clang -target aarch64-none-elf -c -mstrict-align -ffreestanding -mcpu=cortex-a53 -I/Users/dreamliner787-9/TS/microkit-sdk-1.4.0/board/maaxboard/debug/include -I../../../include/ ../../../util/printf.c -o build/printf.o && \
clang -target aarch64-none-elf -c -mstrict-align -ffreestanding -mcpu=cortex-a53 -I/Users/dreamliner787-9/TS/microkit-sdk-1.4.0/board/maaxboard/debug/include -I../../../include/ ../../../util/putchar_debug.c -o build/putchar_debug.o && \

clang -target aarch64-none-elf -c -mstrict-align -ffreestanding -mcpu=cortex-a53 -I/Users/dreamliner787-9/TS/microkit-sdk-1.4.0/board/maaxboard/debug/include -I../../../include/ ../../../drivers/clock/imx/timer.c -o build/timer.o && \

clang -target aarch64-none-elf -c -mstrict-align -ffreestanding -mcpu=cortex-a53 -I/Users/dreamliner787-9/TS/microkit-sdk-1.4.0/board/maaxboard/debug/include -I../../../include/ client.c -o build/client.o && \

python3 create_iomuxc_config.py imx8mq-evk dts/maaxboard.dts build && \
aarch64-none-elf-as build/pinmux_config_data.s -o build/pinmux_config_data.o && \
clang -target aarch64-none-elf -c -mstrict-align -ffreestanding -mcpu=cortex-a53 -I/Users/dreamliner787-9/TS/microkit-sdk-1.4.0/board/maaxboard/debug/include -I../../../include/ iomuxc.c -o build/driver.o && \

ld.lld -L/Users/dreamliner787-9/TS/microkit-sdk-1.4.0/board/maaxboard/debug/lib -lmicrokit -Tmicrokit.ld build/driver.o build/putchar_debug.o build/pinmux_config_data.o build/printf.o -o build/iomuxc.elf && \

ld.lld -L/Users/dreamliner787-9/TS/microkit-sdk-1.4.0/board/maaxboard/debug/lib -lmicrokit -Tmicrokit.ld build/printf.o build/putchar_debug.o build/timer.o -o build/timer.elf && \

ld.lld -L/Users/dreamliner787-9/TS/microkit-sdk-1.4.0/board/maaxboard/debug/lib -lmicrokit -Tmicrokit.ld build/printf.o build/putchar_debug.o build/client.o -o build/client.elf && \

/Users/dreamliner787-9/TS/microkit-sdk-1.4.0/bin/microkit iomuxc.system --search-path build --board maaxboard --config debug -o build/sel4-image --report build/report.txt && \
# scp build/sel4-image billn@tftp:/tftpboot/maaxboard_billn/sel4-image

mq.sh run -s maaxboard2 -f build/sel4-image -c "ABCXYZ"
 