// #include <sel4/sel4.h>
#include <stdint.h>

struct resources {
	uint64_t rx_free;
	uint64_t rx_active;
	uint64_t tx_free;
	uint64_t tx_active;
	uint64_t rx_buffer_data_region;
	uint64_t tx_buffer_data_region;

	uint8_t timer_id;
	uint8_t rx_id;
	uint8_t tx_id;
};

struct resources resources;

void sddf_init(void);
void sddf_notified(unsigned int id);
