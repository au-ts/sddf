#include <stdint.h>
#include <sddf/blk/queue.h>
#include <sddf/blk/config.h>
#include <sddf/resources/device.h>

__attribute__((__section__(".device_resources"))) device_resources_t device_resources;
__attribute__((__section__(".blk_driver_config"))) blk_driver_config_t config;

blk_queue_handle_t blk_queue;

void blk_queue_init_helper() {
    blk_queue_init(&blk_queue, config.virt.req_queue.vaddr, config.virt.resp_queue.vaddr, config.virt.num_buffers);

    blk_storage_info_t *storage_info = config.virt.storage_info.vaddr;
    storage_info->sector_size = 512;
    storage_info->block_size = 1;
    storage_info->capacity = 0xFFFFFFFFFF;
    storage_info->ready = true;
}

uint64_t blk_device_regs_vaddr() {
    return (uint64_t)device_resources.regions[0].region.vaddr;
}

uint64_t blk_device_init_data_vaddr() {
    return (uint64_t)device_resources.regions[1].region.vaddr;
}

uint64_t blk_device_init_data_ioaddr() {
    return (uint64_t)device_resources.regions[1].io_addr;
}

/* Sets the blk_config->ready shared variable and returns currently set value */
bool blk_queue_set_ready(bool ready) {
    blk_config->ready = ready;
    return blk_config->ready;
}

uint8_t blk_queue_empty_req_helper() {
    return blk_queue_empty_req(&blk_queue);
}

uint8_t blk_queue_full_resp_helper() {
    return blk_queue_full_resp(&blk_queue);
}

uint8_t blk_enqueue_resp_helper(uint8_t status, uint16_t success, uint32_t id) {
    // It would be better if we do not use int but use int8_t
    if (blk_enqueue_resp(&blk_queue, status, success, id) == 0) {
        return 0;
    }
    return 1;
}

uint8_t blk_dequeue_req_helper(uint8_t *code, uintptr_t *io_or_offset, uint64_t *block_number, uint16_t *count, uint32_t *id) {
    // It would be better if we do not use int but use int8_t
    // uint16_t temp_count = 0;
    if (blk_dequeue_req(&blk_queue, (blk_req_code_t *)code, io_or_offset, block_number, count, id) == 0) {
        return 0;
    }
    // *count = temp_count;
    return 1;
}
