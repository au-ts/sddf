#!/usr/bin/env python3
# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause


def reset_terminal():
    print("\n\x1b[0m", end="")


class LockedBoardException(Exception):
    """Board is locked and we were told not to poll."""


class TestFailureException(Exception):
    """Test failed"""
