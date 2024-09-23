/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

/* This file is used to put our client framebuffer image into program memory */

.section .fb_img, "aw", @progbits
.global _fb_img, _fb_img_end
_fb_img:
.incbin FB_IMG_PATH
_fb_img_end:
