# QEMU Version

Please ensure that you have the latest version of QEMU installed. This driver
is tested using version 9.0. Please note that the default QEMU version on
Ubuntu distributions is version 6.2. This will not work with our vhost-user
front-end and back-end.

# I2C Backend Daemon

We use the following I2C backend daemon:
https://github.com/rust-vmm/vhost-device/tree/main/vhost-device-i2c.

Please clone this repository and build the vhost-device-i2c daemon.
Follow the instructions in the README.md of this repository.