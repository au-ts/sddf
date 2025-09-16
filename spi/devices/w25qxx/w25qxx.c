/*
 * Copyright 2025, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <sddf/spi/devices/w25qxx.h>

inline static w25qxx_cmd_t _pack_cmd(w25qxx_inst_t inst, uint32_t addr)
{
    return (w25qxx_cmd_t) { .inst = inst,
                            .addr = {
            // Switch the addr from little to big-endian
                                (addr & 0xFF0000) >> 16,
                                (addr & 0x00FF00) >> 8,
                                (addr & 0x0000FF) >> 0,
                            } };
}

inline static uint32_t _cmd_addr(w25qxx_cmd_t cmd)
{
    return (cmd.addr[0] == 0xFF && cmd.addr[1] == 0xFF && cmd.addr[2] == 0xFF)
             ? -1
             :
        // Switch the addr from big to little-endian
               ((uint32_t)cmd.addr[2]) << 0 | ((uint32_t)cmd.addr[1]) << 8 | ((uint32_t)cmd.addr[0]) << 16;
}

inline static int _enqueue_cmd(w25qxx_conf_t *conf, w25qxx_cmd_t cmd, bool final_cmd)
{
    conf->data->cmd[conf->cmd_idx] = cmd;
    return spi_enqueue_write(conf->libspi_conf, &conf->data->cmd[conf->cmd_idx++],
                             _cmd_addr(cmd) == -1 ? sizeof(cmd.inst) : sizeof(w25qxx_cmd_t), !final_cmd);
}

inline static int _block(w25qxx_conf_t *conf)
{
    spi_notify(conf->libspi_conf);

    spi_resp_t resp;
    spi_read_resp(conf->libspi_conf, &resp);

    conf->cmd_idx = 0;

    // TODO
    return 0;
}

// Public interface

int w25qxx_reset(w25qxx_conf_t *conf)
{
    _enqueue_cmd(conf, _pack_cmd(W25QXX_INST_ENABLE_RESET, -1), false);
    _enqueue_cmd(conf, _pack_cmd(W25QXX_INST_RESET_DEVICE, -1), true);

    return _block(conf);
}

int w25qxx_get_ids(w25qxx_conf_t *conf, uint8_t *manufacturer_id, uint16_t *device_id)
{
    _enqueue_cmd(conf, _pack_cmd(W25QXX_INST_JEDEC_ID, -1), false);
    spi_enqueue_read(conf->libspi_conf, conf->data->internal_data, 3, false);

    _block(conf);

    uint32_t id = conf->data->internal_data[0];

    *manufacturer_id = id & 0xFF;
    // Switch endianess from big to little-endian
    *device_id = (id & 0x00FF00) | (id & 0xFF0000) >> 16;

    return 0;
}

int w25qxx_read(w25qxx_conf_t *conf, uint32_t addr, void *buffer, uint16_t len)
{
    if (buffer < (void *)conf->data->data) {
        return -1;
    }

    _enqueue_cmd(conf, _pack_cmd(W25QXX_INST_READ_DATA, addr), false);
    spi_enqueue_read(conf->libspi_conf, buffer, len, false);

    return _block(conf);
}

int w25qxx_write_en(w25qxx_conf_t *conf)
{
    _enqueue_cmd(conf, _pack_cmd(W25QXX_INST_WRITE_ENABLE, -1), true);
    return _block(conf);
}

int w25qxx_program_page(w25qxx_conf_t *conf, uint32_t addr, void *buffer, uint16_t len)
{
    if (buffer < (void *)conf->data->data) {
        return -1;
    }

    uint16_t bytes_until_aligned = ALIGN(addr, W25QXX_PG_SZ) - addr;
    //TODO
    bytes_until_aligned = (bytes_until_aligned) ? bytes_until_aligned : W25QXX_PG_SZ;
    if (len > bytes_until_aligned) {
        return -1;
    }

    w25qxx_write_en(conf);
    _enqueue_cmd(conf, _pack_cmd(W25QXX_INST_PAGE_PROGRAM, addr), false);
    spi_enqueue_write(conf->libspi_conf, buffer, len, false);

    return _block(conf);
}

uint8_t w25qxx_get_status_reg_1(w25qxx_conf_t *conf)
{
    _enqueue_cmd(conf, _pack_cmd(W25QXX_INST_READ_STATUS_REGISTER_1, -1), false);
    spi_enqueue_read(conf->libspi_conf, conf->data->internal_data, 1, false);

    _block(conf);

    return conf->data->internal_data[0];
}

void w25qxx_erase_chip(w25qxx_conf_t *conf)
{
    w25qxx_write_en(conf);
    _enqueue_cmd(conf, _pack_cmd(W25QXX_INST_CHIP_ERASE, -1), true);

    _block(conf);

    uint32_t status;
    do {
        status = w25qxx_get_status_reg_1(conf);
        LOG_W25QXX("STATUS_REG_1=%02X\n", status);
    } while (W25QXX_STATUS_BUSY(status));
}

void w25qxx_erase_block64kb(w25qxx_conf_t *conf, uint32_t addr)
{
    w25qxx_write_en(conf);
    _enqueue_cmd(conf, _pack_cmd(W25QXX_INST_BLOCK_ERASE_64KB, addr), true);

    _block(conf);

    uint32_t status;
    do {
        status = w25qxx_get_status_reg_1(conf);
        LOG_W25QXX("STATUS_REG_1=%02X\n", status);
    } while (W25QXX_STATUS_BUSY(status));
}

void w25qxx_global_unlock(w25qxx_conf_t *conf)
{
    w25qxx_write_en(conf);
    _enqueue_cmd(conf, _pack_cmd(W25QXX_INST_GLOBAL_BLOCK_SECTOR_UNLOCK, -1), true);

    _block(conf);
}
