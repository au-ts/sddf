# BLK_DRIVER_DIR := $(realpath $(dir $(lastword $(MAKEFILE_LIST))))

# blk_driver.elf: blk/ahci/blk_driver.o
# 	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

# blk/ahci/blk_driver.o: ${BLK_DRIVER_DIR}/ahci.c |blk/ahci
# 	$(CC) -c $(CFLAGS) -o $@ $<

# -include blk/ahci/blk_driver.d

# blk/ahci:
# 	mkdir -p $@

# clean::
# 	rm -f blk/ahci/blk_driver.[do]

# clobber::
# 	rm -rf blk/ahci

BLK_DRIVER_DIR := $(realpath $(dir $(lastword $(MAKEFILE_LIST))))

blk_driver.elf: blk/ahci/ahci.o blk/ahci/pcie.o
	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

blk/ahci/ahci.o: ${BLK_DRIVER_DIR}/ahci.c | blk/ahci
	${CC} ${CFLAGS} ${CFLAGS_blk} -o $@ -c $<

blk/ahci/pcie.o: ${BLK_DRIVER_DIR}/pcie.c | blk/ahci
	${CC} ${CFLAGS} ${CFLAGS_blk} -o $@ -c $<


clean::
	rm -f blk/ahci/ahci.[od] blk/ahci/pcie.[od]

clobber::
	rm -f blk/ahci

-include blk/ahci/ahci.d
-include blk/ahci/pcie.d

# SRC := $(wildcard $(BLK_DRIVER_DIR)/*.c)
# OBJ := $(patsubst $(BLK_DRIVER_DIR)/%.c,blk/ahci/%.o,$(SRC))

# blk_driver.elf: $(OBJ)
# 	$(LD) $(LDFLAGS) $^ $(LIBS) -o $@

# blk/ahci/%.o: $(BLK_DRIVER_DIR)/%.c | blk/ahci
# 	$(CC) -c $(CFLAGS) -o $@ $<






























-include $(OBJ:.o=.d)

blk/ahci:
	mkdir -p $@

clean::
	rm -f blk/ahci/*.[do]

clobber::
	rm -rf blk/ahci

