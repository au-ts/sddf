# Copyright 2026, UNSW
# SPDX-License-Identifier: BSD-2-Clause


def is_pow_2(x: int) -> bool:
    return x > 0 and x & (x - 1) == 0


def next_pow_2(n: int) -> int:
    return 1 << ((n - 1).bit_length())
