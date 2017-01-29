include ../Makefile.common

ASYNC_HOST ?= 0
USE_BINDS ?= 1

BINDS_VLOG_0 =
BINDS_VLOG_1 = vlog +define+SIM_ONLY -cuname binds -mfcu \
                    $(TICK2TRADE_ROOT_DIR)/rtl/binds/avalon_if_bind.sv \
                    $(TICK2TRADE_ROOT_DIR)/rtl/binds/host_interface_bind.sv \
                    $(TICK2TRADE_ROOT_DIR)/rtl/binds/hpb_if_bind.sv \
                    $(TICK2TRADE_ROOT_DIR)/rtl/binds/hpb_bind.sv \
                    $(TICK2TRADE_ROOT_DIR)/rtl/binds/rcb_bind.sv \
                    $(TICK2TRADE_ROOT_DIR)/rtl/binds/sef_bind.sv \
                    $(TICK2TRADE_ROOT_DIR)/rtl/binds/cmp_bind.sv \
                    $(TICK2TRADE_ROOT_DIR)/rtl/binds/tts_bind.sv
BINDS_VLOG   = $(BINDS_VLOG_$(USE_BINDS))

BINDS_TOP_0 =
BINDS_TOP_1 = binds
BINDS_TOP   = $(BINDS_TOP_$(USE_BINDS))


build: build_avalon build_feed build_symbol_map build_host build_order build_dut
	vlog $(TICK2TRADE_ROOT_DIR)/tb/feed_tb/feed_env_pkg.sv
	vlog $(TICK2TRADE_ROOT_DIR)/tb/strategy_tb/strategy_env_pkg.sv \
       $(TICK2TRADE_ROOT_DIR)/tests/strategy_seqs/strategy_seq_pkg.sv
	vlog $(TICK2TRADE_ROOT_DIR)/tb/system_tb/system_env_pkg.sv \
       $(TICK2TRADE_ROOT_DIR)/tests/system_seqs/system_seq_pkg.sv \
       $(TICK2TRADE_ROOT_DIR)/tests/system_tests/system_test_pkg.sv
	$(BINDS_VLOG)
	vlog $(TICK2TRADE_ROOT_DIR)/tb/system_tb/tb.sv
	vopt tb $(BINDS_TOP) $(VOPT_OPT_ARGS) -G HPB_ASYNC_HOST=$(ASYNC_HOST) \
	     -o tb_opt
	vopt tb $(BINDS_TOP) $(VOPT_DBG_ARGS) -G HPB_ASYNC_HOST=$(ASYNC_HOST) +acc \
       -o tb_dbg

TESTS = sanity_test basic_test all_messages_test
$(TESTS): 
	make run TESTNAME=$@

regression: clean build $(TESTS) ucdb report