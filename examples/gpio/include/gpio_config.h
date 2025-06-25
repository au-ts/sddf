/*
 * Copyright 2024, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */
#pragma once

/*
NUMBERING SCHEMES

IMX:
- For pins we use 0-31 as thats how many pins per bank
- For irqs write a value > 0 because irq lines are shared.
*/

#define PIN_1 (15) // IMX gpio1_15 // IMX physical 32
#define PIN_2 (13) // IMX gpio1_13 // IMX physical 33

#define IRQ_1 (1)

#define NUM_DRIVER_CHANNELS 62

#define PIN_UNUSED  (-1)
#define IRQ_UNUSED  (-1)

#define UNUSED_CH(n) [n] = { PIN_UNUSED, IRQ_UNUSED }

typedef struct {
    int pin;
    int irq;
} GPIO_driver_channel_t;

// ideally this whole setup should probably be in the meta.py file
static const GPIO_driver_channel_t gpio_driver_channel_mappings[NUM_DRIVER_CHANNELS] = {
    [0] = { PIN_1, IRQ_UNUSED }, // need to claim these channels in meta.py
    [1] = { PIN_2, IRQ_1 },
    UNUSED_CH(2),
    UNUSED_CH(3),
    UNUSED_CH(4),
    UNUSED_CH(5),
    UNUSED_CH(6),
    UNUSED_CH(7),
    UNUSED_CH(8),
    UNUSED_CH(9),
    UNUSED_CH(10),
    UNUSED_CH(11),
    UNUSED_CH(12),
    UNUSED_CH(13),
    UNUSED_CH(14),
    UNUSED_CH(15),
    UNUSED_CH(16),
    UNUSED_CH(17),
    UNUSED_CH(18),
    UNUSED_CH(19),
    UNUSED_CH(20),
    UNUSED_CH(21),
    UNUSED_CH(22),
    UNUSED_CH(23),
    UNUSED_CH(24),
    UNUSED_CH(25),
    UNUSED_CH(26),
    UNUSED_CH(27),
    UNUSED_CH(28),
    UNUSED_CH(29),
    UNUSED_CH(30),
    UNUSED_CH(31),
    UNUSED_CH(32),
    UNUSED_CH(33),
    UNUSED_CH(34),
    UNUSED_CH(35),
    UNUSED_CH(36),
    UNUSED_CH(37),
    UNUSED_CH(38),
    UNUSED_CH(39),
    UNUSED_CH(40),
    UNUSED_CH(41),
    UNUSED_CH(42),
    UNUSED_CH(43),
    UNUSED_CH(44),
    UNUSED_CH(45),
    UNUSED_CH(46),
    UNUSED_CH(47),
    UNUSED_CH(48),
    UNUSED_CH(49),
    UNUSED_CH(50),
    UNUSED_CH(51),
    UNUSED_CH(52),
    UNUSED_CH(53),
    UNUSED_CH(54),
    UNUSED_CH(55),
    UNUSED_CH(56),
    UNUSED_CH(57),
    UNUSED_CH(58),
    UNUSED_CH(59),
    UNUSED_CH(60),
    UNUSED_CH(61),
};