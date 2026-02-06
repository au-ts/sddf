cat \
	../../../util/util.pnk \
	../../../include/sddf/network/queue_header.pnk \
	ethernet_header.pnk \
	../../../include/sddf/network/queue.pnk \
	ethernet.pnk | cpp -P > ethernet_full.pnk
$HOME/Documents/pancake-transpiler-private/target/debug/pancake2viper -I device.vpr -I virtualiser.vpr --allow-undefined-shared --ignore-warnings --incremental --encoding-mode mapped --encoding-mode-map mapping transpile ethernet_full.pnk ethernet.vpr
