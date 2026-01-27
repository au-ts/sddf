#include <microkit.h>
#include <sddf/util/printf.h>
#include <os/sddf.h>
#include <stdint.h>

// djb2 hash: http://www.cse.yorku.ca/~oz/hash.html
unsigned long generate_hash(unsigned char *str)
{
    unsigned long hash = 5381;
    int c;

    while (c = *str++) {
        hash = ((hash << 5) + hash) + c; /* hash * 33 + c */
    }

    return hash;
}

void init(void) {
    char magic[26] = "SCaTRyBCliglbggGhQoDk6UfEn";

    while (true) {
        unsigned long hash = generate_hash(magic);
        sddf_printf("%lu\n", hash);
    }
}