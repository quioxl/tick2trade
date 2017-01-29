## Include common makefile
include ../Makefile.common

USE_BINDS ?= 1

BINDS_VLOG_0 =
BINDS_VLOG_1 = vlog +define+SIM_ONLY -cuname binds -mfcu \
                    $(TICK2TRADE_ROOT_DIR)/rtl/binds/avalon_if_bind.sv
BINDS_VLOG   = $(BINDS_VLOG_$(USE_BINDS))

BINDS_TOP_0 =
BINDS_TOP_1 = binds
BINDS_TOP   = $(BINDS_TOP_$(USE_BINDS))

## Top-level build target for this bench.  Prerequsites are defined in the common makefile.
build: build_avalon build_dut build_feed
	vlog $(TICK2TRADE_ROOT_DIR)/tb/feed_tb/feed_env_pkg.sv $(TICK2TRADE_ROOT_DIR)/tests/feed_tests/feed_test_pkg.sv 
	vlog $(TICK2TRADE_ROOT_DIR)/tb/feed_tb/tb.sv
	$(BINDS_VLOG)
	vopt tb $(BINDS_TOP) $(VOPT_OPT_ARGS) -o tb_opt
	vopt tb $(BINDS_TOP) $(VOPT_DBG_ARGS) -o tb_dbg +acc

TESTS = sanity_test feed_random_test mixed_message_test
$(TESTS): 
	make run TESTNAME=$@

regression: clean build $(TESTS) ucdb report

replay: build
	vlog $(TICK2TRADE_ROOT_DIR)/tb/feed_tb/feed_replay_tb.sv
	vopt feed_replay_tb -o replay_tb_opt +acc
	vsim replay_tb_opt -onfinish stop