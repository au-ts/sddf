/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <microkit.h>
#include <sddf/spi/client.h>
#include <sddf/spi/config.h>
#include <sddf/util/printf.h>
#include <sddf/util/string.h>
#include <sddf/spi/libspi.h>

__attribute__((__section__(".spi_client_config"))) spi_client_config_t spi_config;

#define DEBUG_CLIENT
#ifdef DEBUG_CLIENT
#define LOG_CLIENT(...) do{ sddf_dprintf("SPI_CLIENT|INFO: "); sddf_printf(__VA_ARGS__); }while(0)
#else
#define LOG_CLIENT(...) do{}while(0)
#endif
#define LOG_CLIENT_ERR(...) do{ sddf_printf("SPI_CLIENT|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)

spi_queue_handle_t handle;
libspi_conf_t libspi_conf;
co_control_t libmicrokitco_control;
microkit_cothread_sem_t async_io_semaphore;

#define CS_LINE 2

/* Reserve the first 4 bytes of the slice region for inst + addr for w25qxx commands */
uint8_t *w25qxx_cmd;
void *scratch;

#define STACK_SIZE (4096)
uint8_t client_stack[STACK_SIZE];
uintptr_t stacks[1];

inline static void pack_addr_inst(uint32_t addr, uint8_t inst) {
    uint8_t *addr_byte = (uint8_t *) &addr;
    w25qxx_cmd[3] = addr_byte[0];
    w25qxx_cmd[2] = addr_byte[1];
    w25qxx_cmd[1] = addr_byte[2]; // Addr in big endian
    w25qxx_cmd[0] = inst;
}

void w25qxx_reset(void) {  
    w25qxx_cmd[1] = 0x99, /* Reset */ 
    w25qxx_cmd[0] = 0x66, /* Enable reset inst */ 
    spi_write(&libspi_conf, CS_LINE, w25qxx_cmd, 2);
}

void w25qxx_get_ids(void) {
    *w25qxx_cmd = 0x9F; /* JEDEC ID inst */

    spi_writeread(&libspi_conf, CS_LINE, w25qxx_cmd, 1, scratch + 1, 3);

    uint8_t manufacturer_id = *((uint8_t *) scratch + 1);
    uint16_t device_id = *((uint16_t *) (scratch + 2));
    // Flip the endianess since it is given as big endian
    device_id = (device_id & 0xFF) << 8 | (device_id & 0xFF00) >> 8;

    LOG_CLIENT("Manufacturer ID=%X, Device ID=%X\n", manufacturer_id, device_id);
}

void w25qxx_read(uint32_t addr, void *buffer, uint16_t len) {
    pack_addr_inst(addr, 0x03 /* read data inst */);
    spi_writeread(&libspi_conf, CS_LINE, w25qxx_cmd, 4, buffer, len);
}

void w25qxx_write_en(void) {
    *w25qxx_cmd = 0x06; /* write en inst */
    spi_write(&libspi_conf, CS_LINE, w25qxx_cmd, 1);
}

void w25qxx_write_disable(void) {
    *w25qxx_cmd = 0x04; /* write disable inst */
    spi_write(&libspi_conf, CS_LINE, w25qxx_cmd, 1);
}

#define W25QXX_PG_SZ (256)
#define PG_PROG_INST (0x02)
void w25qxx_write(uint32_t addr, void *buffer, uint16_t len) {
    addr &= 0x00FFFFFF; // TODO: how to deal with >24 bit addrs

    // Write leading bytes to page align subsequent writes (addr, not buffer)
    uint16_t bytes_until_aligned = ALIGN(addr, W25QXX_PG_SZ) - addr;
    uint16_t num_leading_bytes = MIN(len, bytes_until_aligned);
    
    if (num_leading_bytes != 0) {
        w25qxx_write_en(); // must be enabled before every pg program, as it is cleared each time
        pack_addr_inst(addr, PG_PROG_INST);
        spi_writewrite(&libspi_conf, CS_LINE, w25qxx_cmd, 4, buffer, num_leading_bytes);
        
        bool done = num_leading_bytes == len;
        if (done) {
            return;
        }
    }

    // Write as many pages as possible
    void *pages = buffer + num_leading_bytes;
    uint32_t addr_page = addr + num_leading_bytes;
    uint16_t num_pages = (len - num_leading_bytes) / W25QXX_PG_SZ;

    for (uint16_t i = 0; i < num_pages; i++) {
        w25qxx_write_en();
        pack_addr_inst(addr_page + i * W25QXX_PG_SZ, PG_PROG_INST);
        spi_writewrite(&libspi_conf, CS_LINE, w25qxx_cmd, 4, pages + i * W25QXX_PG_SZ, 
            W25QXX_PG_SZ);
    }

    // Write trailing bytes if they exist
    void *trailing_bytes = buffer + num_leading_bytes + num_pages * W25QXX_PG_SZ;
    uint32_t addr_trailing_bytes = addr + num_leading_bytes + num_pages * W25QXX_PG_SZ;
    uint16_t num_trailing_bytes = (len - num_leading_bytes) % W25QXX_PG_SZ;

    if (num_trailing_bytes != 0) {
        w25qxx_write_en();
        pack_addr_inst(addr_trailing_bytes, PG_PROG_INST);
        spi_writewrite(&libspi_conf, CS_LINE, w25qxx_cmd, 4, trailing_bytes, num_trailing_bytes);
    }
}

uint32_t w25qxx_get_status(void) {
    const uint8_t STATUS_INST[] = {
        0x15, /* read status register 3 inst */
        0x35, /* read status register 2 inst */
        0x05, /* read status register 1 inst */
    };

    for (int i = 0; i < sizeof(STATUS_INST); i++) {
        *w25qxx_cmd = STATUS_INST[i];
        spi_writeread(&libspi_conf, CS_LINE, w25qxx_cmd, 1, scratch + i, 1);
    }

    return *((uint32_t *) scratch);
}

void w25qxx_erase_chip(void) {
    w25qxx_write_en();
    *w25qxx_cmd = 0xC7; /* erase chip inst */
    spi_write(&libspi_conf, CS_LINE, w25qxx_cmd, 1);

    uint32_t status;
    while ((status = w25qxx_get_status()) & BIT(0) /* status register 1, bit 0 is the BUSY bit */) {
        LOG_CLIENT("STATUS=%06X\n", status);
    }
} 

void w25qxx_erase_block64kb(uint32_t addr) {
    w25qxx_write_en();
    pack_addr_inst(addr, 0xD8 /* 64kb block erase inst */); 
    spi_write(&libspi_conf, CS_LINE, w25qxx_cmd, 1);

    uint32_t status;
    while ((status = w25qxx_get_status()) & BIT(0) /* status register 1, bit 0 is the BUSY bit */) {
        LOG_CLIENT("STATUS=%06X\n", status);
    }
}

void client_main(void) {
    assert(spi_config_check_magic(&spi_config));

    // Initialize PD state
    handle = spi_queue_init(spi_config.virt.req_queue.vaddr, spi_config.virt.resp_queue.vaddr);
    libspi_init(&libspi_conf, &handle);
    w25qxx_cmd = spi_config.slice.vaddr;
    scratch = spi_config.slice.vaddr + sizeof(uint64_t);

    // Claim the 2nd CS line 
    assert(spi_bus_claim(spi_config.virt.id, CS_LINE, SPI_CPOL_LOW, SPI_CPHA_FIRST));

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

