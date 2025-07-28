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

extern microkit_cothread_sem_t async_io_semaphore;

#define LOG_LIBSPI_ERR(...) do{ sddf_printf("LIBSPI|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)

typedef spi_client_config_t libspi_conf_t;

spi_err_t spi_enqueue_write(libspi_conf_t *conf, void *write_buf, uint16_t len, bool cs_active_after_cmd);
spi_err_t spi_enqueue_read(libspi_conf_t *conf, void *read_buf, uint16_t len, bool cs_active_after_cmd);
spi_err_t spi_enqueue_transfer(libspi_conf_t *conf, void *read_buf, void *write_buf, uint16_t len, bool cs_active_after_cmd);
spi_err_t spi_enqueue_dummy(libspi_conf_t *conf, uint16_t len, bool cs_active_after_cmd);
int spi_notify(libspi_conf_t *conf);
int spi_read_resp(libspi_conf_t *conf, spi_resp_t *resp);

