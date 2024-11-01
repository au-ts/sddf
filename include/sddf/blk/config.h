#include <stdint.h>
#include <sddf/blk/queue.h>

struct blk_client_config {
    blk_storage_info_t *storage_info;
    blk_req_queue_t *req_queue;
    blk_resp_queue_t *resp_queue;
    uintptr_t data;
    uint64_t queue_capacity;
};
