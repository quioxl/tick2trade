## Include common makefile
include ../Makefile.common

## Top-level build target for this bench.  Prerequsites are defined in the common makefile.
build: build_avalon build_dut build_feed
	vlog $(TICK2TRADE_ROOT_DIR)/tb/feed_tb/feed_env_pkg.sv $(TICK2TRADE_ROOT_DIR)/tests/feed_tests/feed_test_pkg.sv 
	vlog $(TICK2TRADE_ROOT_DIR)/tb/feed_tb/tb.sv $(TICK2TRADE_ROOT_DIR)/tb/feed_tb/feed_recorder.sv
	vopt tb -o tb_opt
	vopt tb -o tb_dbg +acc

