cat \
	../../../util/util.pnk \
	../../../include/sddf/network/queue_header.pnk \
	ethernet_header.pnk \
	../../../include/sddf/network/queue.pnk \
	ethernet.pnk | cpp -P > ethernet_full.pnk
pancake2viper -I device.vpr -I virtualiser.vpr -I ethernet_hard_import.vpr --allow-undefined-shared --ignore-warnings transpile ethernet_full.pnk ethernet.vpr
sed -i -e 's/:= bv64_to_int(bv64_or(bv64_from_int(x_126), bv64_from_int(8192)))/:= _f_or_WRAP(x_126)/' ethernet.vpr
