class sanity_test extends system_test_base;
  `uvm_component_utils(sanity_test)

  function new(string name = "sanity_test", uvm_component parent = null);
    super.new(name,parent);
  endfunction

  virtual task run_phase(uvm_phase phase);
    random_host_program_seq host_seq_h;
    feed_simple_seq feed_seq_h;

    
    super.run_phase(phase);
    host_seq_h = random_host_program_seq::type_id::create("host_seq_h");
    host_seq_h.start(env_h.host_agent_h.seqr_h);
    feed_seq_h = feed_simple_seq::type_id::create("seq_h");
    feed_seq_h.start(env_h.layering_h.feed_message_seqr_h);
    #1us;
    phase.drop_objection(this);
  endtask

endclass