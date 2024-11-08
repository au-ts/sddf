#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause

CLK_DRIVER_DIR := $(dir $(lastword $(MAKEFILE_LIST)))
CLK_DRIVER_COMMON_DIR := $(SDDF)/drivers/clk
CLK_CONFIG_HEADER := $(BUILD_DIR)/clk_config.h
CLK_DRIVER_CONF_INC := $(SDDF)/include/sddf/clk
CLK_DRIVER_INC := $(CLK_DRIVER_DIR)/include

CLK_DRIVER_OBJS := clk.o clk-operations.o clk-imx8mq.o clk-imx.o

clk_driver.elf: $(CLK_DRIVER_OBJS) libsddf_util_debug.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@


$(CLK_DRIVER_OBJS): ${CLK_DRIVER_COMMON_DIR}/*.c ${CLK_DRIVER_DIR}/*.c $(CLK_CONFIG_HEADER)
	$(CC) -c $(CFLAGS) \
		-I${CLK_DRIVER_INC} \
		-I${CLK_DRIVER_CONF_INC} \
		-I${CLK_DRIVER_COMMON_DIR} \
		-I${BUILD_DIR} \
		-I${UART_DRIVER_DIR}/include \
		-I${CLK_DRIVER_COMMON_DIR} $^

$(CLK_CONFIG_HEADER): $(DTS_FILE) $(CLK_DRIVER_COMMON_DIR)/create_clk_config.py
	$(PYTHON) $(CLK_DRIVER_COMMON_DIR)/create_clk_config.py $(DTS_FILE) $(BUILD_DIR)

clean::
	rm -f clk_driver.o

clobber::
	rm -rf clk_driver.elf
