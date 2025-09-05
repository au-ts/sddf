/*
 * Copyright 2025, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <sddf/spi/libspi.h>

#define DEBUG_W25QXX
#ifdef DEBUG_W25QXX
#define LOG_W25QXX(...) do{ sddf_dprintf("W25QXX|INFO: "); sddf_printf(__VA_ARGS__); }while(0)
#else
#define LOG_W25QXX(...) do{}while(0)
#endif
#define LOG_W25QXX_ERR(...) do{ sddf_printf("W25QXX|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)

typedef struct w25qxx_cmd {
    uint8_t inst;
    uint8_t addr[3];
} w25qxx_cmd_t;

typedef struct w25qxx_layout {
    w25qxx_cmd_t cmd[3];
    uint32_t internal_data[1];
    uint32_t data[];
} w25qxx_layout_t;

typedef struct w25qxx_conf {
    libspi_conf_t *libspi_conf;
    w25qxx_layout_t *data;
    uint8_t cmd_idx;
} w25qxx_conf_t;

typedef enum w25qxx_inst {
    W25QXX_INST_WRITE_ENABLE = 0x06,
    W25QXX_INST_JEDEC_ID = 0x9F,
    W25QXX_INST_READ_DATA = 0x03,
    W25QXX_INST_PAGE_PROGRAM = 0x02,
    W25QXX_INST_BLOCK_ERASE_64KB = 0xD8,
    W25QXX_INST_CHIP_ERASE = 0xC7,
    W25QXX_INST_READ_STATUS_REGISTER_1 = 0x05,
    W25QXX_INST_READ_STATUS_REGISTER_2 = 0x35,
    W25QXX_INST_READ_STATUS_REGISTER_3 = 0x15,
    W25QXX_INST_GLOBAL_BLOCK_SECTOR_UNLOCK = 0x98,
    W25QXX_INST_ENABLE_RESET = 0x66,
    W25QXX_INST_RESET_DEVICE = 0x99,
} w25qxx_inst_t;

#define W25QXX_PG_SZ (256)
#define W25QXX_STATUS_BUSY(status) ((status) & BIT(0))

int w25qxx_reset(w25qxx_conf_t *conf);
int w25qxx_get_ids(w25qxx_conf_t *conf, uint8_t *manufacturer_id, uint16_t *device_id);
int w25qxx_read(w25qxx_conf_t *conf, uint32_t addr, void *buffer, uint16_t len);
int w25qxx_write_en(w25qxx_conf_t *conf);
int w25qxx_program_page(w25qxx_conf_t *conf, uint32_t addr, void *buffer, uint16_t len);
uint8_t w25qxx_get_status_reg_1(w25qxx_conf_t *conf);
void w25qxx_erase_chip(w25qxx_conf_t *conf);
void w25qxx_erase_block64kb(w25qxx_conf_t *conf, uint32_t addr);
void w25qxx_global_unlock(w25qxx_conf_t *conf);
