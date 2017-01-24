TESTNAME ?= feed_random_test

SEED ?= 0

DEBUG ?= 0
VSIM_OPTS_0 = -c -do "run -a;quit" -uvmcontrol=none tb_opt
VSIM_OPTS_1 = -onfinish stop -classdebug -uvmcontrol=all tb_dbg -do "log -r /*; do feed_tb_wave.do; run 0"
VSIM_OPTS = $(VSIM_OPTS_$(DEBUG))

clean:
	rm -rf *.log *~ *.bak work transcript *.wlf design.bin qwave.db

build_avalon: 
	vlog ../sv/avalon/avalon_if.sv ../sv/avalon/avalon_pkg.sv 

build_feed_tb: build_avalon
	vlog ../tb/feed_tb/feed_env_pkg.sv ../tests/feed_tests/feed_test_pkg.sv ../tb/feed_tb/tb.sv
	vopt tb -o tb_opt
	vopt tb -o tb_dbg +acc

build: build_feed_tb

run:
	vsim -solvefaildebug +UVM_TESTNAME=$(TESTNAME) $(VSIM_OPTS) -sv_seed $(SEED)