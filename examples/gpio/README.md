# TODO

Finish Driver:
- workout how mapping of channels to gpio pins is going to work
- i think only giving the option to configure 43 pins is completely fine
- using a config file is probs a good idea (but need a way to validate it)


CONFIG FILE DRAFT
will have CONSTANT 40 * 3 array

```
---------------------------------------------
| channel number | pin (int)   | client num |
---------------------------------------------
|       20       |    3        |     0      |
---------------------------------------------
|       21       |    2        |     2      |
---------------------------------------------
|       22       |    23       |     2      |
---------------------------------------------
|       23       |    9        |     3      |
---------------------------------------------
|       24       |    50       |     5      |
---------------------------------------------
....
---------------------------------------------
|       62       |    -1       |      -1    |
---------------------------------------------
```

pins must use the linear scheme inside of meson/gpio.h
maybe initialise pin and client num to -1

hence driver can check if its not implemented

driver know what clients have what gpios so clinets can't just set
an irq channel they own to any gpio they want (this is the client num part of the table)



- config file will need driver channel -> gpio pin so driver can use,
- another issue is if driver needs to select pin for irq channel
    driver will need to see if client has access to that gpio pin
    hence there needs to be a way to valiadate that





build a client
 - test output driving an led
 - test input by pressing a button
 - make sure the make files are working

then add to i2c device class

create a pull request

# do the irqs need to be edge?

# go back and try remove repeated code




