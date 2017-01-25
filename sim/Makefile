TESTNAME ?= feed_random_test

SEED ?= 0

DEBUG ?= 0
VSIM_OPTS_0 = -c -do "run -a;quit" -uvmcontrol=none tb_opt
VSIM_OPTS_1 = -onfinish stop -classdebug -uvmcontrol=all tb_dbg -do "log -r /*; do $(WAVEFILE); run 0"
VSIM_OPTS = $(VSIM_OPTS_$(DEBUG))

clean:
	rm -rf *.log *~ *.bak work transcript *.wlf design.bin qwave.db pkg_lib feed_tb_work certe_dump.xml 

build_avalon: 
	vlog -work pkg_lib ../sv/avalon/avalon_if.sv ../sv/avalon/avalon_pkg.sv 

build_dut:
	vlog -work dut_lib -f design.f

build_feed_tb: build_avalon build_dut
	vlog -work pkg_lib ../tb/feed_tb/feed_env_pkg.sv ../tests/feed_tests/feed_test_pkg.sv 
	vlog -L pkg_lib -work feed_tb_work ../tb/feed_tb/tb.sv
	vopt tb -L feed_tb_work -L pkg_lib -L dut_lib -work feed_tb_work -o tb_opt
	vopt tb -L feed_tb_work -L pkg_lib -L dut_lib -work feed_tb_work -o tb_dbg +acc

run_feed_tb: 
	$(eval WAVEFILE := feed_tb_wave.do)
	vsim -work feed_tb_work -solvefaildebug +UVM_TESTNAME=$(TESTNAME) $(VSIM_OPTS) -sv_seed $(SEED)

build: build_feed_tb
run: run_feed_tb