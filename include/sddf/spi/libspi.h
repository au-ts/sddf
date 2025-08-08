/*
 * Copyright 2025, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */
// SPI interface library for clients.
// Provides helper functions for creating transactions and handing them to the virtualiser.
//
// See spi/queue.h for details about the SPI transport layer.

// WARNING:: the event cothread is assumed to be available whenever a blocking function is called!
//           Be aware of possible danger if your client performs complex multitasking.

#pragma once
#include <stdint.h>
#include <sddf/util/printf.h>
#include <sddf/spi/queue.h>
#include <sddf/spi/config.h>
#include <libmicrokitco.h>

#ifdef DEBUG_LIBSPI
#define LOG_LIBSPI(...) do{ sddf_dprintf("CLIENT|INFO: "); sddf_printf(__VA_ARGS__); }while(0)
#else
#define LOG_LIBSPI(...) do{}while(0)
#endif
#define LOG_LIBSPI_ERR(...) do{ sddf_printf("LIBSPI|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)

extern microkit_cothread_sem_t async_io_semaphore;

typedef spi_client_config_t libspi_conf_t;

spi_status_t spi_enqueue_write(libspi_conf_t *conf, void *write_buf, uint16_t len, bool cs_active_after_cmd);
spi_status_t spi_enqueue_read(libspi_conf_t *conf, void *read_buf, uint16_t len, bool cs_active_after_cmd);
spi_status_t spi_enqueue_transfer(libspi_conf_t *conf, void *read_buf, void *write_buf, uint16_t len,
                                  bool cs_active_after_cmd);
spi_status_t spi_enqueue_dummy(libspi_conf_t *conf, uint16_t len, bool cs_active_after_cmd);
spi_status_t spi_notify(libspi_conf_t *conf);
spi_status_t spi_read_resp(libspi_conf_t *conf, spi_resp_t *resp);
