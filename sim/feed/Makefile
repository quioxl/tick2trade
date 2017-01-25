include ../Makefile.common

build: build_avalon build_dut
	vlog $(TICK2TRADE_ROOT_DIR)/tb/feed_tb/feed_env_pkg.sv $(TICK2TRADE_ROOT_DIR)/tests/feed_tests/feed_test_pkg.sv 
	vlog $(TICK2TRADE_ROOT_DIR)/tb/feed_tb/tb.sv $(TICK2TRADE_ROOT_DIR)/tb/feed_tb/feed_recorder.sv
	vopt tb -o tb_opt
	vopt tb -o tb_dbg +acc

