<!--
    Copyright 2024, UNSW

    SPDX-License-Identifier: BSD-2-Clause
-->

# GPIO example

This example makes use two circuits.

I need to use a resistor otherwise too much current might be pulled
this is from ohms law V = IR
hence small resistance (from gpio pin and led) and 3.3 - 2v neans big current
Use a resistor that accounts for the LEDs forward voltage
and see

The ODROID-C4 provides 40-pin dual row expansion header “J2”. All signals on the expansion headers are 3.3V except for the analog input signal.

Circuit 1:

GPIO_H --------|>|----[R]-------- GND
               LED


Circuit 2:

GPIO_X ----[ ]---- VCC (3.3)
          Button

# TODO
get rid of value in set pin
should be pretty clear they arent trying to do something else
this could even be done inside of the initialisation of the driver and hence doesnt even need a set request!!!!!!!






