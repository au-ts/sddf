#
# Copyright 2024, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause

CLK_DRIVER_DIR := $(dir $(lastword $(MAKEFILE_LIST)))
CLK_CONFIG_HEADER := $(BUILD_DIR)/clk_config.h
CLK_DRIVER_CONF_INC := $(SDDF)/include/sddf/clk
CLK_DRIVER_INC := $(CLK_DRIVER_DIR)/include
CLK_DRIVER_COMMON_DIR := $(SDDF)/drivers/clk/

CLK_DRIVER_BOARD_SOURCES := clk-imx.c clk-imx8mq.c
CLK_DRIVER_COMMON_SOURCES := clk.c clk-operations.c
CLK_DRIVER_SOURCES := $(addprefix $(CLK_DRIVER_DIR), $(CLK_DRIVER_BOARD_SOURCES)) \
                      $(addprefix $(CLK_DRIVER_COMMON_DIR), $(CLK_DRIVER_COMMON_SOURCES))
CLK_DRIVER_OBJS = $(patsubst $(CLK_DRIVER_COMMON_DIR)%.c, clk_driver/%.o, $(CLK_DRIVER_SOURCES))

$(CLK_DRIVER_OBJS): CFLAGS += -I${CLK_DRIVER_INC} \
		-I${CLK_DRIVER_CONF_INC} \
		-I${BUILD_DIR} \
		-I${UART_DRIVER_DIR}/include \
		-I${CLK_DRIVER_COMMON_DIR}
clk_driver/%.o: $(CLK_DRIVER_COMMON_DIR)/%.c $(CLK_CONFIG_HEADER)
	mkdir -p $(dir $@)
	$(CC) -c $(CFLAGS) -o $@ $<

clk_driver.elf: $(CLK_DRIVER_OBJS) libsddf_util_debug.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

$(CLK_CONFIG_HEADER): $(DTS_FILE) $(CLK_DRIVER_COMMON_DIR)/create_clk_config.py
	$(PYTHON) $(CLK_DRIVER_COMMON_DIR)/create_clk_config.py $(DTS_FILE) $(BUILD_DIR)

clean::
	rm -f clk_driver.o

clobber::
	rm -rf clk_driver.elf
