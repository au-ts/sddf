#
# Copyright 2023, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause
#
# This Makefile snippet builds the serial RX and TX virtualisers
# it should be included into your project Makefile
#
# NOTES:
#  Generates serial_virt_rx.elf serial_virt_tx.elf
#

SERIAL_IMAGES:= serial_virt_rx.elf serial_virt_tx.elf

serial/components/virt_%x_pnk.o: serial/components/virt_%x_pnk.S |serial/components
	$(CC) -c $(CFLAGS) -o $@ $<

serial/components/virt_%x_pnk.S: serial/components/virt_%x_pnk.pnk |serial/components
	$(PANCAKE_COMPILER) $(PANCAKE_FLAGS) < $< > $@

serial/components/virt_%x_pnk.pnk: ${SDDF}/util/util.pnk ${SDDF}/include/sddf/serial/queue.pnk ${SDDF}/include/sddf/serial/config.pnk ${SDDF}/serial/components/virt_%x.pnk |serial/components
	cat $^ | $(CPP) -P -CC -nostdinc > $@

serial/components/virt_%x_init_pnk.o: ${SDDF}/serial/components/virt_%x_init_pnk.c |serial/components $(SDDF_LIBC_INCLUDE)
	$(CC) -c $(CFLAGS) -I${SERIAL_DRIVER_DIR}/include -I ${SDDF}/serial/components/include -o $@ $<

serial/components/virt_%x_pre.o: ${SDDF}/serial/components/virt_%x.c |serial/components $(SDDF_LIBC_INCLUDE)
	${CC} ${CFLAGS} -I ${SDDF}/include -I ${SDDF}/serial/components/include -o $@ -c $<

serial/components/virt_%x.o: serial/components/virt_%x_pre.o
	$(OBJCOPY) --redefine-sym init=c_init --redefine-sym notified=c_notified $< $@

serial_virt_%x.elf: serial/components/virt_%x_pnk.o serial/components/virt_%x.o serial/components/virt_%x_init_pnk.o util/pancake_ffi.o util/pancake_common.o libsddf_util_debug.a
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

serial/components:
	mkdir -p $@

clean::
	rm -f serial/components/virt_[rt]x_pnk.[od] serial/components/virt_[rt]x_pnk.S serial/components/virt_[rt]x_pnk.pnk serial/components/virt_[rt]x_init_pnk.[od] serial/components/virt_[rt]x_pre.[od] serial/components/serial_virt_[rt]x.

clobber:: clean
	rm -f ${SERIAL_IMAGES}

-include serial/components/serial_virt_rx.d
-include serial/components/serial_virt_tx.d
