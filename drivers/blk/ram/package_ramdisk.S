/*
 * Copyright 2024, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

// This file include the ramdisk as a blob of memory.
// So you can create the partition table offline and build it into 
// the image at compile time.

#if defined(RAMDISK_IMAGE_PATH)
.section .ramdisk_image, "aw", @progbits
.global _ramdisk_begin, _ramdisk_end
_ramdisk_begin:
.incbin RAMDISK_IMAGE_PATH
_ramdisk_end:
#endif