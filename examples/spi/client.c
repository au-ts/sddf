/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <microkit.h>
#include <string.h>
#include <sddf/spi/config.h>
#include <sddf/util/printf.h>
#include <sddf/spi/libspi.h>
#include <sddf/spi/devices/w25qxx.h>

__attribute__((__section__(".spi_client_config"))) spi_client_config_t spi_config;

#define DEBUG_CLIENT
#ifdef DEBUG_CLIENT
#define LOG_CLIENT(...) do{ sddf_dprintf("SPI_CLIENT|INFO: "); sddf_printf(__VA_ARGS__); }while(0)
#else
#define LOG_CLIENT(...) do{}while(0)
#endif
#define LOG_CLIENT_ERR(...) do{ sddf_printf("SPI_CLIENT|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)

co_control_t libmicrokitco_control;
microkit_cothread_sem_t async_io_semaphore;

#define STACK_SIZE (4096)
uint8_t client_stack[STACK_SIZE];
uintptr_t stacks[1];

void client_main(void)
{
    libspi_conf_t *conf = (libspi_conf_t *)&spi_config;
#define W25QXX
#ifndef W25QXX
    uint8_t *data = spi_config.data.vaddr;
    int len = 65;
    for (int i = 0; i < len; i++) {
        data[i] = i;
    }

    spi_status_t err = spi_enqueue_transfer(conf, data + 0x1000, data, len, false);
    LOG_CLIENT("err=%s\n", spi_status_str(err));
//    spi_enqueue_read(conf, data + 0x1000, len, false);
    spi_notify(conf);
    spi_resp_t resp;
    spi_read_resp(conf, &resp);
    LOG_CLIENT("resp=%s\n", spi_status_str(resp.status));
    for (int i = 0; i < len; i++) {
        LOG_CLIENT("read_data[%3d]=%3d\n", i, ((uint8_t *)data + 0x1000)[i]);
    }

#else
    w25qxx_conf_t dev_conf = { conf, spi_config.data.vaddr, 0 };
    void *data = dev_conf.data->data;

    w25qxx_reset(&dev_conf);

    uint8_t manufacturer_id;
    uint16_t device_id;
    w25qxx_get_ids(&dev_conf, &manufacturer_id, &device_id);
    LOG_CLIENT("manufacturer_id=%x, device_id=%x\n", manufacturer_id, device_id);
    LOG_CLIENT("status_reg_1=%02X\n", w25qxx_get_status_reg_1(&dev_conf));

    w25qxx_global_unlock(&dev_conf);
    w25qxx_erase_block64kb(&dev_conf, 0x23);

    for (uint32_t i = 0; i < 256 * 4; i++) {
        ((uint8_t *)data)[i] = i;
    }

    for (uint32_t i = 0; i < 4; i++) {
        w25qxx_program_page(&dev_conf, i * W25QXX_PG_SZ, data + i * W25QXX_PG_SZ, W25QXX_PG_SZ);
    }

    w25qxx_read(&dev_conf, 0x0, data + 0x1000, 4 * W25QXX_PG_SZ);

    for (uint32_t i = 0; i < 4 * W25QXX_PG_SZ / sizeof(uint32_t); i++) {
        uint32_t *stuff = ((uint32_t *)(data + 0x1000));
        LOG_CLIENT("%03X: %08X\n", i, stuff[i]);
    }

#endif
}

void init(void)
{
    LOG_CLIENT("initializing\n");

    assert(spi_config_check_magic(&spi_config));
    stacks[0] = (uintptr_t)&client_stack;

    // Setup cothreads
    microkit_cothread_init(&libmicrokitco_control, STACK_SIZE, stacks);
    microkit_cothread_spawn(client_main, NULL);
    microkit_cothread_semaphore_init(&async_io_semaphore);
    microkit_cothread_yield();
}

void notified(microkit_channel ch)
{
    LOG_CLIENT("notified on ch %d\n", ch);
    if (ch == spi_config.virt.id) {
        microkit_cothread_semaphore_signal(&async_io_semaphore);
    } else {
        LOG_CLIENT_ERR("Spuriously notified on %d\n", ch);
    }
}
