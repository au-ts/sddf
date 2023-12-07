#include <stdint.h>

void write_command(uint8_t *header, uint8_t hlen, const uint8_t *body, uint8_t blen);
uint8_t read_response(uint8_t *buffer, uint8_t buffer_len);
