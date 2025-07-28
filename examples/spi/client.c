/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <microkit.h>
#include <sddf/spi/config.h>
#include <sddf/util/printf.h>
#include <sddf/util/string.h>
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

void client_main(void) {
    libspi_conf_t *conf = (libspi_conf_t *) &spi_config;
    uint8_t *data = spi_config.data.vaddr;
    int len = 64;
    for (int i = 0; i < len; i++) {
        data[i] = i;
    }

    spi_err_t err = spi_enqueue_transfer(conf, data + 0x1000, data, len, false);
    LOG_CLIENT("err=%s\n", err_to_str(err));
    spi_notify(conf);
    spi_resp_t resp;
    spi_read_resp(conf, &resp);
    LOG_CLIENT("resp=%s\n", err_to_str(resp.err));
    for (int i = 0; i < len; i++) {
        LOG_CLIENT("read_data[%3d]=%3d\n", i, ((uint8_t *) data + 0x1000)[i]);
    }

    #ifdef W25QXX
    assert(spi_config_check_magic(&spi_config));

    // Initialize PD state
    w25qxx_cmd = spi_config.slice.vaddr;
    scratch = spi_config.slice.vaddr + sizeof(uint64_t);

    w25qxx_reset();
    w25qxx_get_ids(); 

    LOG_CLIENT("STATUS=%06X\n", w25qxx_get_status());

    //w25qxx_erase_chip();
    w25qxx_erase_block64kb(0x23);

    // fill scratch
    for (uint32_t i = 0; i <= 0x1FF; i++) {
        ((uint8_t *) scratch)[i] = i;
    }

    w25qxx_write(0x23, scratch, 0x1FF);

    w25qxx_read(0x23, scratch + 0x800, 0x1FF);

    for (uint32_t i = 0; i <= 0x1FF / sizeof(uint32_t); i++) {
        uint32_t *stuff = ((uint32_t *) (scratch + 0x800));
        LOG_CLIENT("%03X: %08X\n", i, stuff[i]);
    }

//    for (int i = 0; i < 16; i++) 
//        LOG_CLIENT("Iteration %d\n", i + 1);
//        for (int j = 0; j < 0x100 / sizeof(uint64_t); j++) {
//            LOG_CLIENT("\t%lX\n", ((uint64_t *) (slice + 0x800))[j]);
//        }
//    }
    #endif
}

void init(void) {
    LOG_CLIENT("initializing\n");

    stacks[0] = (uintptr_t) &client_stack;

    // Setup cothreads
    microkit_cothread_init(&libmicrokitco_control, STACK_SIZE, stacks);
    microkit_cothread_spawn(client_main, NULL);
    microkit_cothread_semaphore_init(&async_io_semaphore);
    microkit_cothread_yield();
}

void notified(microkit_channel ch) {
    LOG_CLIENT("notified on ch %d\n", ch);
    if (ch == spi_config.virt.id) {
        microkit_cothread_semaphore_signal(&async_io_semaphore);
    }
    else {
        LOG_CLIENT_ERR("Spuriously notified on %d\n", ch);
    }
}

