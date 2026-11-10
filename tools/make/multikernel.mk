# Copyright 2026, UNSW
#
# SPDX-License-Identifier: BSD-2-Clause

MULTIKERNEL_MANIFEST := multikernel/kernels.json
MULTIKERNEL_NAMES := $(shell $(PYTHON) -c \
	'import json, sys; print(*(p["name"] for p in sorted(json.load(open(sys.argv[1])), key=lambda p:p["hart"])))' \
	"$(MULTIKERNEL_CONFIG)")

ifeq ($(strip $(MULTIKERNEL_NAMES)),)
$(error MULTIKERNEL_CONFIG must partition the kernels)
endif

IMAGE_FILE := $(addprefix multikernel/,$(addsuffix .elf,$(MULTIKERNEL_NAMES)))
REPORT_FILE := $(IMAGE_FILE:.elf=-report.txt)
METAPROGRAM_ARGS := --multikernel "$(MULTIKERNEL_CONFIG)"

.DELETE_ON_ERROR:
all qemu: $(IMAGE_FILE) $(REPORT_FILE)

$(MULTIKERNEL_MANIFEST) : $(MULTIKERNEL_CONFIG)

$(IMAGE_FILE) $(REPORT_FILE) &: $(MULTIKERNEL_MANIFEST) $(IMAGES) \
        $(wildcard *.elf multikernel/*.system multikernel/*.overlay.dts *.data) \
        $(DTS) $(SDDF)/tools/build_multikernel.py
	$(PYTHON) $(SDDF)/tools/build_multikernel.py \
	    --sel4 $(SEL4_SRC) --microkit $(MICROKIT_SRC) \
	    --board $(MICROKIT_BOARD) --config $(MICROKIT_CONFIG) --dts $(DTS) \
	    --directory $(BUILD_DIR)/multikernel $(MULTIKERNEL_BUILD_ARGS)
