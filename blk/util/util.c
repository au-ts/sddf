#include <sddf/blk/util.h>

void *memset(void *dest, int c, size_t n)
{
    unsigned char *s = dest;
    for (; n; n--, s++) {
        *s = c;
    }
    return dest;
}
