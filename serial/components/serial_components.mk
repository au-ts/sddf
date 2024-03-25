#
# Copyright 2023, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# This Makefile snippet builds the serial RX and TX virtualisers
# it should be included into your project Makefile
#
# It relies on the variable SERIAL_NUM_CLIENTS to configure the virtualisers
#

ifeq ($(strip $(SERIAL_NUM_CLIENTS)),)
$(error Specify the number of clients for the serial virtualisers.  Expect -DSERIAL_NUM_CLIENTS=3 or similar)
endif
ifeq ($(strip $(UART_DRIVER)),)
$(error The serial virtualisers need headers from the UART source. PLease specify UART_DRIVER)
endif

CFLAGS_serial := -I ${SDDF}/include -I${UART_DRIVER}/include -I${SDDF}/util/include ${SERIAL_NUM_CLIENTS} 
serial_rx_virt.elf: virt_rx.o #
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@
serial_tx_virt.elf: virt_tx.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

virt_rx.o: ${SDDF}/serial/components/virt_rx.c
	${CC} ${CFLAGS} ${CFLAGS_serial} -o $@ -c ${SERIAL_NUM_CLIENTS} $<

virt_tx.o: ${SDDF}/serial/components/virt_tx.c
	${CC} ${CFLAGS} ${CFLAGS_serial} -o $@ -c ${SERIAL_NUM_CLIENTS} $<

clean::
	rm -f mux_[rt]x.[od]

clobber::
	rm -f serial_rx_virt.elf serial_tx_virt.elf


-include mux_rx.d
-include mux_tx.d
