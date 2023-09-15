// Simple test client PD for I2C

#include <sel4cp.h>

#include "i2c.h"
#include "printf.h"
#include "i2c-transport.h"



void init(void) {
    sel4cp_dbg_puts("I2C client init\n");
}


void notified(sel4cp_channel c) {

}