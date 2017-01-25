include ../Makefile.common

build: build_avalon build_symbol_map build_host build_dut
	vlog $(TICK2TRADE_ROOT_DIR)/tb/strategy_tb/strategy_env_pkg.sv $(TICK2TRADE_ROOT_DIR)/tests/strategy_tests/strategy_test_pkg.sv 
	vlog $(TICK2TRADE_ROOT_DIR)/tb/strategy_tb/tb.sv
	vopt tb -o tb_opt
	vopt tb -o tb_dbg +acc

