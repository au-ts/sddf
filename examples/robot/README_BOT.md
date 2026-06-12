<!--
    Copyright 2024, UNSW

    SPDX-License-Identifier: BSD-2-Clause
-->

# LionsOS Robot

This example is the piece of software that runs on the LionsOS Robot. It makes use of a handful of drivers to read from sensors on the robot and send motor commands to drive the robot. This example utilises the budget/period mechanisms to demonstrate mixed-criticality, particularly between higher criticality control loop and lower criticality data transmission.

As well as autonomous obstacle avoidance, this project allows for remote control of the robot via BLE. 

## TODO: link LionsOS robot repo

## System architecture
The following diagram shows the system architecture of the robot example (TODO: insert image). The arrows of the diagram point in the direction of data flow. The Robot utilises the serial, GPIO, PWM, timer, and I2C (on the odroid version to communicate with an IMU) subsytems to execute various tasks. The GPIO driver is used to read from three ultrasonic sensors and an encoder attached to one of the robot's motors (TODO: check if we're reading anything else). In addition, the PWM driver is used to send signals to the motor driver to control the robot's motors while the timer is used to keep track of completed tasks in the client.

TODO: explain i2c usage

## Building

The following platforms are supported:
* maaxboard

To compile the system image, run:
```sh
make MICROKIT_SDK=/Users/michaeltanto/Documents/Programming/TS/microkit-sdk-2.1.0 MICROKIT_BOARD=maaxboard MICROKIT_CONFIG=(benchmark/release/debug)
```

The system image will be generated at `build/loader.img`

## Running

This example must be run on a MaaxBoard. If running on the robot, the MaaxBoard's boot command has been configured to fetch the image at `tftp.keg.cse.unsw.edu.au:/home/tftp/maaxboard_michaeltanto/robot.img`. Make sure to scp the image generated from building the project to this location:

```sh
scp path-to/robot/build/loader.img tftp.keg.cse.unsw.edu.au:/home/tftp/maaxboard_michaeltanto/robot.img 
```

To turn on the robot, follow the commands listed on the robot's hardware page:
(TODO: link hardware page)

