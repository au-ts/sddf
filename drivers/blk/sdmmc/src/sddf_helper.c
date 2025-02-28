#include <sddf/blk/queue.h>
#include <blk_config.h>
#include <stdint.h>

blk_queue_handle_t queue_handle_memory;
blk_queue_handle_t *queue_handle = &queue_handle_memory;

blk_req_queue_t *blk_req_queue;
blk_resp_queue_t *blk_resp_queue;

blk_storage_info_t *blk_config;

void blk_queue_init_helper() {
    blk_queue_init(queue_handle, blk_req_queue, blk_resp_queue, BLK_QUEUE_CAPACITY_DRIV);
    blk_config->sector_size = 512;
    blk_config->block_size = 1;
    blk_config->capacity = 0xFFFFFFFFFF;
    blk_config->ready = true;
}

uint8_t blk_queue_empty_req_helper() {
    return blk_queue_empty_req(queue_handle);
}

uint8_t blk_queue_full_resp_helper() {
    return blk_queue_full_resp(queue_handle);
}

uint8_t blk_enqueue_resp_helper(uint8_t status, uint16_t success, uint32_t id) {
    // It would be better if we do not use int but use int8_t
    if (blk_enqueue_resp(queue_handle, status, success, id) == 0) {
        return 0;
    }
    return 1;
}

uint8_t blk_dequeue_req_helper(uint8_t *code, uintptr_t *io_or_offset, uint32_t *block_number, uint16_t *count, uint32_t *id) {
    // It would be better if we do not use int but use int8_t
    // uint16_t temp_count = 0;
    if (blk_dequeue_req(queue_handle, (blk_req_code_t *)code, io_or_offset, block_number, count, id) == 0) {
        return 0;
    }
    // *count = temp_count;
    return 1;
}

/*
uint8_t blk_dequeue_req_helper(uint8_t *code, uintptr_t *io_or_offset, uint32_t *block_number, uint16_t *count, uint32_t *id) {
 
    if (blk_dequeue_req(queue_handle, (blk_req_code_t *)code, io_or_offset, block_number, count, id) == 0) {
        return 0;
    }
    return 1;
}

// Why this version does not work????
uint8_t blk_dequeue_req_helper(uint8_t *code, uintptr_t *io_or_offset, uint32_t *block_number, uint32_t *count, uint32_t *id) {

    uint16_t temp_count = 0;
    if (blk_dequeue_req(queue_handle, (blk_req_code_t *)code, io_or_offset, block_number, &temp_count, id) == 0) {
        return 0;
    }
    *count = temp_count;
    return 1;
}
*/