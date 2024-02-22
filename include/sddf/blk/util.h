#include <stddef.h>

// @ericc: When we have libc implementation replace this
static void *memcpy(void *restrict dest, const void *restrict src, size_t n)
{
    unsigned char *d = dest;
    const unsigned char *s = src;
    for (; n; n--) {
        *d++ = *s++;
    }
    return dest;
}
/* We need an externally linked memset definition for
   copying structs */
void *memset(void *dest, int c, size_t n);