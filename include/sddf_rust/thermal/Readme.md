## Thermal Sensor Driver Interface

The Thermal Sensor Driver provides an interface for querying temperatures and setting thermal alarm thresholds.

### Procedure: `get_sensor_num`

Retrieves the number of thermal sensors managed by this driver.

*   **Signature:** `procedure get_sensor_num()`
*   **Description:** Returns the total number of available thermal sensor channels. This allows clients to discover and iterate over all sensors. Channels are zero-indexed (i.e., from `0` to `N-1`).
*   **Parameters:**
    *   None.
*   **Returns:**
    *   An integer representing the count of available sensor channels.

### Procedure: `get_temperature`

Reads the temperature from a specific sensor.

*   **Signature:** `procedure get_temperature(sensor_channel)`
*   **Description:** Reads the current temperature from the specified sensor channel. To maintain precision without using floating-point numbers, the temperature is always returned in **milli-Celsius** (i.e., degrees Celsius multiplied by 1000).
*   **Parameters:**
    *   `sensor_channel`: An integer specifying the zero-based index of the sensor to read.
*   **Returns:**
    *   On success, returns an integer representing the temperature in milli-Celsius.
    *   On failure, returns an error code.
*   **Possible Errors:**
    *   `Invalid Channel`: The specified `sensor_channel` does not exist.
    *   `Hardware Error`: A problem occurred while communicating with the sensor hardware.

### Procedure: `set_alarm_temp`

Sets a high-temperature alarm threshold for a sensor.

*   **Signature:** `procedure set_alarm_temp(sensor_channel, alarm_temp)`
*   **Description:** Configures a temperature threshold for a specific sensor. If the sensor's temperature reading exceeds this value, the driver is responsible for sending a notification via PPC to the registered thermal governor. The threshold must be specified in **milli-Celsius**.
*   **Parameters:**
    *   `sensor_channel`: An integer specifying the zero-based index of the sensor to configure.
    *   `alarm_temp`: The temperature threshold in milli-Celsius.
*   **Returns:**
    *   On success, returns nothing.
    *   On failure, returns an error code.
*   **Possible Errors:**
    *   `Invalid Channel`: The specified `sensor_channel` does not exist.
    *   `Invalid Temperature`: The `alarm_temp` is outside the range supported by the hardware.
    *   `Hardware Error`: A problem occurred while communicating with the sensor hardware.

#### Design Rationale and Implementation Flexibility

The `set_alarm_temp` interface is designed to be broadly compatible with a variety of thermal sensor hardware, from modern SoCs to simpler microcontrollers. This is achieved by supporting two primary implementation strategies within the driver, abstracting the hardware differences from the rest of the system.

**Case 1: Hardware-Assisted Alarms**

For most modern sensors that support hardware-based temperature thresholds, the driver implementation is straightforward and efficient.
1.  The driver receives the `set_alarm_temp` call and programs the hardware's threshold registers with the `alarm_temp` value.
2.  When the temperature exceeds this limit, the hardware **automatically generates an interrupt (IRQ)**.
3.  The driver's interrupt handler receives the IRQ and then sends the notification to the thermal governor.
This approach is highly efficient as it requires no CPU cycles for polling.

**Case 2: Software-Based Alarms (Polling)**

For simpler hardware that lacks built-in alarm capabilities, the interface can be implemented using a software-polling approach.
1.  The driver receives the `set_alarm_temp` call and stores the `alarm_temp` value internally.
2.  It then requests a periodic timer from the OS kernel (e.g., to wake up every 500ms or 1s).
3.  On each timer-based wakeup, the driver reads the current temperature using its internal logic.
4.  It compares the current temperature to the stored `alarm_temp`.
5.  If the threshold is exceeded, it sends the PPC notification to the governor.

This dual-implementation strategy ensures that a single, consistent OS-level interface can be used by high-level components, **decoupling system thermal policy from specific hardware implementation details**. The governor simply sets an alarm and waits for a notification, regardless of how the driver accomplishes the task.