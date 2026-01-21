<!--
    Copyright 2025, UNSW

    SPDX-License-Identifier: BSD-2-Clause
-->

# Spin models

This directory contains a set of
[Spin](https://spinroot.com/spin/whatispin.html) models of each of the
networking components in the echo server system. They are written in Spin's
modelling language PROMELA. These models were created during the development of
the [signalling protocol](/docs/developing.md#signalling-protocol) which
dictates when components are required to notify their neighbours.

The signalling protocol used in the networking subsystem is optimised to
minimise the number unnecessary notifications, while the protocol itself, as
represented in the models, is proven to be deadlock free.
