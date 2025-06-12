## PWM Fan Driver Interface

The PWM Fan Driver provides a standardized way to control the speed of one or more system fans connected via Pulse-Width Modulation (PWM).

### Procedure: `config_fan_speed`

Sets the fan's rotational speed to one of the predefined levels.

*   **Signature:** `procedure config_fan_speed(speed)`
*   **Description:** This procedure commands the fan hardware to operate at a specified speed level. The driver translates the abstract speed level into a hardware-specific PWM signal.
*   **Parameters:**
    *   `speed`: One of the predefined speed levels (`Stopped`, `Low`, `Medium`, `High`, `Full`).
*   **Returns:**
    *   None. This is a "fire-and-forget" operation. The operation should always succeed.

### Predefined Speed Levels

To simplify fan control, the interface uses a set of predefined speed levels instead of raw percentage or PWM values. The driver is responsible for mapping these levels to the correct hardware-specific duty cycle.

| Level Name | Underlying Value (0-255) | Description                      |
| :--------- | :------------------------- | :------------------------------- |
| `Stopped`  | 0                          | Fan is completely off (0% speed) |
| `Low`      | 64                         | Low-speed operation (~25%)       |
| `Medium`   | 128                        | Medium-speed operation (~50%)    |
| `High`     | 192                        | High-speed operation (~75%)      |
| `Full`     | 255                        | Maximum-speed operation (100%)   |
