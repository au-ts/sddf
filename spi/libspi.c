/*
 * Copyright 2025, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <sddf/spi/libspi.h>

static spi_status_t _spi_cmd_validate(size_t read_offset, size_t write_offset, uint16_t len, uint64_t data_region_size)
{
    bool reading = read_offset != -1;
    bool writing = write_offset != -1;
    size_t read_end = read_offset + CMD_LEN(len);
    size_t write_end = write_offset + CMD_LEN(len);

    bool read_unaligned = reading && (read_offset & sizeof(uint32_t) - 1) != 0;
    bool write_unaligned = writing && (write_offset & sizeof(uint32_t) - 1) != 0;
    if (read_unaligned || write_unaligned) {
        return SPI_STATUS_ERR_CMD_UNALIGNED_OFFSET;
    }

    bool read_oob = reading && read_end >= data_region_size;
    bool write_oob = writing && write_end >= data_region_size;
    if (read_oob || write_oob) {
        return SPI_STATUS_ERR_CMD_OOB;
    }

    bool partial_overlap = reading && writing
                        && ((write_offset < read_offset && read_offset < write_end)
                            || (read_offset < write_offset && write_offset < read_end));
    if (partial_overlap) {
        return SPI_STATUS_ERR_CMD_PARTIAL_OVERLAP;
    }

    return SPI_STATUS_OK;
}

spi_status_t spi_enqueue_write(libspi_conf_t *conf, void *write_buf, uint16_t len, bool cs_active_after_cmd)
{
    return spi_enqueue_transfer(conf, NULL, write_buf, len, cs_active_after_cmd);
}

spi_status_t spi_enqueue_read(libspi_conf_t *conf, void *read_buf, uint16_t len, bool cs_active_after_cmd)
{
    return spi_enqueue_transfer(conf, read_buf, NULL, len, cs_active_after_cmd);
}

spi_status_t spi_enqueue_transfer(libspi_conf_t *conf, void *read_buf, void *write_buf, uint16_t len,
                                  bool cs_active_after_cmd)
{
    size_t read_offset = (read_buf) ? read_buf - conf->data.vaddr : -1;
    size_t write_offset = (write_buf) ? write_buf - conf->data.vaddr : -1;
    spi_status_t err = _spi_cmd_validate(read_offset, write_offset, len, conf->data.size);
    if (err != SPI_STATUS_OK) {
        return err;
    }

    spi_handle_t handle;
    assert(spi_handle_init(&handle, conf->virt.cmd_queue.vaddr, conf->virt.resp_queue.vaddr, NULL, NULL,
                           conf->virt.queue_capacity_bits));
    return spi_enqueue_cmd(&handle, read_offset, write_offset, len, cs_active_after_cmd) ? SPI_STATUS_ERR_CMD_QUEUE_FULL
                                                                                         : SPI_STATUS_OK;
}

spi_status_t spi_enqueue_dummy(libspi_conf_t *conf, uint16_t len, bool cs_active_after_cmd)
{
    return spi_enqueue_transfer(conf, NULL, NULL, len, cs_active_after_cmd);
}

spi_status_t spi_notify(libspi_conf_t *conf)
{
    spi_cmd_queue_t *queue = conf->virt.cmd_queue.vaddr;
    if (queue->element[queue->tail].cs_active_after_cmd) {
        return SPI_STATUS_ERR_PARTIAL_TXN;
    }

    microkit_deferred_notify(conf->virt.id);
    microkit_cothread_semaphore_wait(&async_io_semaphore);
    return SPI_STATUS_OK;
}

spi_status_t spi_read_resp(libspi_conf_t *conf, spi_resp_t *resp)
{
    spi_handle_t handle;
    assert(spi_handle_init(&handle, conf->virt.cmd_queue.vaddr, conf->virt.resp_queue.vaddr, NULL, NULL,
                           conf->virt.queue_capacity_bits));
    return spi_dequeue_resp(&handle, &resp->err, &resp->err_cmd_idx) ? SPI_STATUS_ERR_RESP_QUEUE_EMPTY : SPI_STATUS_OK;
}
