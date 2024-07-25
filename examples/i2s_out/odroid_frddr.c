// FRDDR test example
#include <microkit.h>
#include <sddf/util/util.h>
#include <sddf/util/printf.h>
#include <sddf/i2s_output/frddr.h>

// #define DEBUG_VIRTUALISER

#ifdef DEBUG_VIRTUALISER
#define LOG_VIRTUALISER(...) do{ sddf_dprintf("I2s VIRTUALISER|INFO: "); sddf_dprintf(__VA_ARGS__); }while(0)
#else
#define LOG_VIRTUALISER(...) do{}while(0)
#endif

#define LOG_VIRTUALISER_ERR(...) do{ sddf_printf("I2s VIRTUALISER|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)

