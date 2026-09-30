CONFIG_FILE ?= pancake.config

ifeq ($(shell test -f $(CONFIG_FILE) && echo exists), exists)
    include $(CONFIG_FILE)
    
    $(info Loaded PANCAKE config from $(CONFIG_FILE))
    ifneq ($(MICROKIT_SDK),)
        $(info   Build SDK: $(MICROKIT_SDK))
    endif
    ifneq ($(MICROKIT_BOARD),)
        $(info   Build Board: $(MICROKIT_BOARD))
    endif
    ifneq ($(MICROKIT_CONFIG),)
        $(info   Build Config: $(MICROKIT_CONFIG))
    endif
    ifneq ($(CAKE_COMPILER),)
        $(info   CakeML Compiler: $(CAKE_COMPILER))
    endif
    ifneq ($(PANCAKE_NETWORK_DRIVER),)
        $(info   - Network Driver: enabled)
    endif
    ifneq ($(PANCAKE_NETWORK_VIRT_TX),)
        $(info   - Network Virt TX: enabled)
    endif
    ifneq ($(PANCAKE_NETWORK_VIRT_RX),)
        $(info   - Network Virt RX: enabled)
    endif
    ifneq ($(PANCAKE_NETWORK_COPY),)
        $(info   - Network Copy: enabled)
    endif
    ifneq ($(PANCAKE_SERIAL_DRIVER),)
        $(info   - Serial Driver: enabled)
    endif
    ifneq ($(PANCAKE_SERIAL_VIRT_TX),)
        $(info   - Serial Virt TX: enabled)
    endif
    ifneq ($(PANCAKE_SERIAL_VIRT_RX),)
        $(info   - Serial Virt RX: enabled)
    endif
    ifneq ($(PANCAKE_TIMER),)
        $(info   - Timer: enabled)
    endif
else
    $(info config file $(CONFIG_FILE) not found, using environment variables)
endif

export MICROKIT_SDK
export MICROKIT_BOARD
export MICROKIT_CONFIG
export CAKE_COMPILER
export TOOLCHAIN
export PANCAKE_NETWORK_DRIVER
export PANCAKE_NETWORK_VIRT_TX
export PANCAKE_NETWORK_VIRT_RX
export PANCAKE_NETWORK_COPY
export PANCAKE_SERIAL_DRIVER
export PANCAKE_SERIAL_VIRT_TX
export PANCAKE_SERIAL_VIRT_RX
export PANCAKE_TIMER
export PANCAKE_I2C
export PANCAKE_BLK