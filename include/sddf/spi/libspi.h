// SPI interface library for clients.
// Provides helper functions for creating requests and handing them to the virtualiser.
// Enables automatic allocation of command structs, but user is expected to perform management
// of SLICE region to supply buffers as this is not practical to generalise.
//
// Currently this interface only supports single command requests, but the protocol is capable
// of doing many command requests. If your usage requires more commands per request, do not use
// this library and instead implement direct calls to the protocol in <sddf/spi/queue.h>
//
// See spi/queue.h for details about the SPI transport layer.

// WARNING:: the event cothread is assumed to be available whenever a blocking function is called!
//           Be aware of possible danger if your client performs complex multitasking. This library
//           also assumes that nothing else is using the CONTROL or SLICE regions if in use.

#pragma once
#include <stdint.h>
#include <sddf/spi/queue.h>
#include <sddf/util/printf.h>
#include <sddf/spi/config.h>
#include <libmicrokitco.h>

// Client must define this. E.g.
// __attribute__((__section__(".spi_client_config"))) spi_client_config_t spi_config;
extern spi_client_config_t spi_config;

extern microkit_cothread_sem_t async_io_semaphore;

#define SPI_CONTROL_REGION ((uint8_t *)spi_config.control.vaddr)
#define SPI_SLICE_REGION ((uint8_t *)spi_config.slice.vaddr)

#define LOG_LIBSPI_ERR(...) do{ sddf_printf("LIBSPI|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)

//TODO: update 
/*
 * The sDDF SPI protocol reduces all SPI transactions into a series of commands.
 * Commands may designate any of the following operations:
 * 1. A read of N bytes, stored in buffer B.
 * 2. A read of N bytes from device register R, with register cs_line R stored in the first byte of the read buffer B. Overwritten with read data on return.
 * 3. A write of N bytes, supplied by buffer B. Writes to device registers are expressed by
 *    putting the register cs_line in the first byte of the write buffer.
 *
 *  Any of these command types may optionally use the following flags:
 *  * RSTART: repeated start
 *  Other flags are used to describe a read, write or write-read (sub-cs_line read)
 */

//TODO: update
// ########### Command allocator functions ############
// SDFgen will do a lot of the work for us, but unfortunately all of the variables it generates
// are considered runtime-context by the C compiler. As a result, we need to do some magic to
// have a sane allocator which doesn't need a bunch of #defines set based on region sizes.
//
// This allocator sets aside a tracking bitmask from the available room in the control region.
// Commands are 2 words, hence a region of size S can store a max of S/2 commands.
// S/2 commands can be indexed using (S/2)/64 = S/128. We set aside this many bitmask words at
// the base of the region. The remaining C=S - (S/128)=127/128 * S bytes are used to store
// ((127/128)S) / 2 commands.

#define LIBSPI_BITMASK_SZ (spi_config.control.size / sizeof(spi_cmd_t) / 8)

typedef struct libspi_conf {
    spi_queue_handle_t *handle;
    spi_cmd_t *control_start;   // Pointer to first command in control region
} libspi_conf_t;

int libspi_init(libspi_conf_t *conf_struct, spi_queue_handle_t *queue_handle);
int spi_write(libspi_conf_t *conf, spi_cs_line_t cs_line, void *write_buf, uint16_t len);
int spi_read(libspi_conf_t *conf, spi_cs_line_t cs_line, void *read_buf, uint16_t len);
int spi_transfer(libspi_conf_t *conf, spi_cs_line_t cs_line, void *read_buf, void *write_buf,
        uint16_t len);
int spi_writeread(libspi_conf_t *conf, spi_cs_line_t cs_line, void *write_buf, uint16_t write_len,
        void *read_buf, uint16_t read_len);
int spi_writewrite(libspi_conf_t *conf, spi_cs_line_t cs_line, void *write1_buf, 
        uint16_t write1_len, void *write2_buf, uint16_t write2_len);
