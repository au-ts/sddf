/*
 * Copyright 2025, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <sddf/spi/libspi.h>

#ifdef DEBUG_LIBSPI
#define LOG_LIBSPI(...) do{ sddf_dprintf("CLIENT|INFO: "); sddf_printf(__VA_ARGS__); }while(0)
#else
#define LOG_LIBSPI(...) do{}while(0)
#endif

static spi_err_t _spi_cmd_validate(size_t read_offset, size_t write_offset, uint16_t len,
        uint64_t data_region_size) {
    uint32_t proper_len = CMD_LEN(len);

    bool reading = read_offset != -1;
    bool writing = write_offset != -1;
    size_t read_end = read_offset + proper_len;
    size_t write_end = write_offset + proper_len;

    bool read_unaligned = reading && read_offset & sizeof(uint32_t) - 1;
    bool write_unaligned = writing && write_offset & sizeof(uint32_t) - 1;
    if (read_unaligned || write_unaligned) {
        return SPI_ERR_UNALIGNED_OFFSET;
    }

    bool read_oob = reading && read_end >= data_region_size; 
    bool write_oob = writing && write_end >= data_region_size;
    if (read_oob || write_oob) {
        return SPI_ERR_OOB;
    }

    bool partial_overlap = reading && writing && 
        ((write_offset < read_offset  && read_offset  < write_end) || 
         (read_offset  < write_offset && write_offset < read_end ));
    if (partial_overlap) {
        return SPI_ERR_PARTIAL_OVERLAP;
    }

    return SPI_ERR_OK;
}

spi_err_t spi_enqueue_write(libspi_conf_t *conf, void *write_buf, uint16_t len, bool cs_active_after_cmd)
{
    return spi_enqueue_transfer(conf, NULL, write_buf, len, cs_active_after_cmd);
}

spi_err_t spi_enqueue_read(libspi_conf_t *conf, void *read_buf, uint16_t len, bool cs_active_after_cmd)
{
    return spi_enqueue_transfer(conf, read_buf, NULL, len, cs_active_after_cmd);
}

spi_err_t spi_enqueue_transfer(libspi_conf_t *conf, void *read_buf, void *write_buf, uint16_t len, bool cs_active_after_cmd)
{
    size_t read_offset  = (read_buf) ? read_buf  - conf->data.vaddr : -1;
    size_t write_offset = (write_buf) ? write_buf - conf->data.vaddr : -1;
    spi_err_t err = _spi_cmd_validate(read_offset, write_offset, len, conf->data.size);
    if (err != SPI_ERR_OK) {
        return err;
    }
 
    spi_cmd_queue_t *queue = conf->virt.cmd_queue.vaddr;
    return spi_enqueue_cmd(queue, read_offset, write_offset, len, cs_active_after_cmd) ? 
        -1 /*TODO*/ : SPI_ERR_OK;
}

spi_err_t spi_enqueue_dummy(libspi_conf_t *conf, uint16_t len, bool cs_active_after_cmd)
{
    return spi_enqueue_transfer(conf, NULL, NULL, len, cs_active_after_cmd);
}

int spi_notify(libspi_conf_t *conf)
{
    spi_cmd_queue_t *queue = conf->virt.cmd_queue.vaddr;
    if (queue->cmd[queue->ctrl.tail].cs_active_after_cmd) {
        return -1;
    }

    // TODO: is this correct?
    microkit_deferred_notify(conf->virt.id);
    microkit_cothread_semaphore_wait(&async_io_semaphore);
    return 0;
}

int spi_read_resp(libspi_conf_t *conf, spi_resp_t *resp)
{
    return spi_dequeue_resp(conf->virt.resp_queue.vaddr, &resp->err, &resp->err_cmd_idx);
}

