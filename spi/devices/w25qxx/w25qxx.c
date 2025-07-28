#include <include/sddf/spi/devices/w25qxx.h>

#define CMD conf->data->cmd
#define DATA conf->data->data

inline static w25qxx_cmd_t _pack_cmd(w25qxx_inst_t inst, uint32_t addr) {
    return (w25qxx_cmd_t) { 
        .inst = inst;
        .addr = { 
            // Switch the addr from little to big-endian
            (addr & 0xFF0000) >> 16,
            (addr & 0x00FF00) >> 8,
            (addr & 0x0000FF) >> 0,
        }
    };
}

inline static int _enqueue_cmd(w25qxx_conf *conf, w25qxx_cmd_t cmd, bool final_cmd) {
    conf->data->cmd[conf->cmd_idx++] = cmd;
    return spi_enqueue_write(conf->libspi_conf, &conf->data->cmd[conf->cmd_idx], addr == -1 ? 1 : 4, 
        !final_cmd);
}

inline static int _block(w25qxx_conf_t *conf) {
    spi_notify(conf->libspi_conf);
    
    spi_resp_t resp;
    spi_read_resp(conf->libspi_conf, &resp);

    conf->cmd_idx = 0;

    // TODO
    return 0;
}

// Public interface

int w25qxx_reset(w25qxx_conf_t *conf) {  
    _enqueue_cmd(conf, _pack_cmd(W25QXX_INST_ENABLE_RESET, -1), false);
    _enqueue_cmd(conf, _pack_cmd(W25QXX_INST_RESET_DEVICE, -1), true);

    return _block(conf->libspi_conf);
}

int w25qxx_get_ids(w25qxx_conf_t *conf, uint8_t *manufacturer_id, uint16_t *device_id) {
    _enqueue_cmd(conf, _pack_cmd(W25QXX_INST_JEDEC_ID, -1), false);
    spi_enqueue_read(conf->libspi_conf, DATA, 3, false);

    _block(conf->libspi_conf);

    uint32_t id = DATA[0];

    *manufacturer_id = id & 0xFF;
    // Switch endianess from big to little-endian
    *device_id = 
        (id & 0x00FF00) | 
        (id & 0xFF0000) >> 16;

    return 0;
}

int w25qxx_read(w25qxx_conf_t *conf, uint32_t addr, void *buffer, uint16_t len) {
    if (buffer < DATA) {
        return -1;
    }

    _enqueue_cmd(conf, _pack_cmd(W25QXX_INST_READ_DATA, addr), false);
    spi_enqueue_read(conf->libspi_conf, buffer, len, false);

    return _block(conf->libspi_conf);
}

int w25qxx_write_en(w25qxx_conf_t *conf) {
    return _enqueue_cmd(conf, _pack_cmd(W25QXX_INST_WRITE_ENABLE, -1), false);
}

int w25qxx_program_page(w25qxx_conf_t *conf, uint32_t addr, void *buffer, uint16_t len) {
    if (buffer < DATA) {
        return -1;
    }

    uint16_t bytes_until_aligned = ALIGN(addr, W25QXX_PG_SZ) - addr;
    if (len > bytes_until_aligned) {
        return -1;
    }

    w25qxx_write_en(conf);
    _enqueue_cmd(conf, _pack_cmd(W25QXX_INST_PAGE_PROGRAM), false);
    spi_enqueue_write(conf->libspi_conf, buffer, len, false);

    return _block(conf->libspi_conf);
}

uint32_t w25qxx_get_status(void) {
    _enqueue_cmd(conf, _pack_cmd(W25QXX_INST_READ_STATUS_REGISTER_1, -1), false);
    spi_enqueue_read(conf->libspi_conf, &DATA[0], 1, false);
    _enqueue_cmd(conf, _pack_cmd(W25QXX_INST_READ_STATUS_REGISTER_2, -1), false);
    spi_enqueue_read(conf->libspi_conf, &DATA[1], 1, false);
    _enqueue_cmd(conf, _pack_cmd(W25QXX_INST_READ_STATUS_REGISTER_3, -1), false);
    spi_enqueue_read(conf->libspi_conf, &DATA[2], 1, false);

    _block(conf->libspi_conf);

    return ((DATA[2] & 0xFF) << 16) |
           ((DATA[1] & 0xFF) <<  8) | 
           ((DATA[0] & 0xFF) <<  0);
}

void w25qxx_erase_chip(void) {
    w25qxx_write_en();
    _enqueue_cmd(conf, _pack_cmd(W25QXX_INST_CHIP_ERASE, -1), true);

    uint32_t status;
    do {
        status = w25qxx_get_status();
        LOG_CLIENT("STATUS=%06X\n", status);
    } while (W25QXX_STATUS_BUSY(status));
} 

void w25qxx_erase_block64kb(uint32_t addr) {
    w25qxx_write_en();
    _enqueue_cmd(conf, _pack_cmd(W25QXX_INST_BLOCK_ERASE_64KB, -1), true);

    uint32_t status;
    do {
        status = w25qxx_get_status();
        LOG_CLIENT("STATUS=%06X\n", status);
    } while (W25QXX_STATUS_BUSY(status));
}

