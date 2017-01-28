class basic_test extends strategy_test_base;
  `uvm_component_utils(basic_test)

  function new(string name = "basic_test", uvm_component parent = null);
    super.new(name,parent);
  endfunction : new

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    //Turn off the new order generator to prevent the RAM from changing
    cfg_h.enable_new_order_gen = 0;
    cfg_h.order_cfg_h.stall_frequency = 0;
  endfunction : build_phase

  virtual task run_phase(uvm_phase phase);
    incr_host_program_seq host_seq_h;
    feed_symbol_match_seq feed_sym_seq_h;
    
    super.run_phase(phase);
    host_seq_h = incr_host_program_seq::type_id::create("host_seq_h");
    host_seq_h.start(env_h.host_agent_h.seqr_h);
    feed_sym_seq_h = feed_symbol_match_seq::type_id::create("feed_sym_seq_h");
    feed_sym_seq_h.trans_count = 20;
    messege_sent_count += feed_sym_seq_h.trans_count;
    feed_sym_seq_h.start(env_h.master_agent_h.seqr_h);
    #1us;
    phase.drop_objection(this);
  endtask : run_phase

endclass : basic_test