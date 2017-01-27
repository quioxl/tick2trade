include ../Makefile.common

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
	vlog $(TICK2TRADE_ROOT_DIR)/tb/strategy_tb/strategy_env_pkg.sv \
       $(TICK2TRADE_ROOT_DIR)/tests/strategy_seqs/strategy_seq_pkg.sv \
       $(TICK2TRADE_ROOT_DIR)/tests/strategy_tests/strategy_test_pkg.sv
	$(BINDS_VLOG)
	vlog $(TICK2TRADE_ROOT_DIR)/tb/strategy_tb/tb.sv
	vopt tb $(BINDS_TOP) -o tb_opt
	vopt tb $(BINDS_TOP) -o tb_dbg +acc

