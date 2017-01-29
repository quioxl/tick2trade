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
    `uvm_info("MESSAGES", $sformatf("%0d symbols will be programmed in strategy RAM", host_seq_h.trans_count), UVM_LOW)
    symbols_programmed = host_seq_h.trans_count;
    host_seq_h.start(env_h.host_agent_h.seqr_h);
    feed_seq_h = feed_simple_seq::type_id::create("seq_h");
    `uvm_info("MESSAGES", $sformatf("%0d messages will be sent", feed_seq_h.trans_count + 1), UVM_LOW)
    messege_sent_count += (feed_seq_h.trans_count + 1);
    feed_seq_h.start(env_h.layering_h.feed_message_seqr_h);
    #1us;
    phase.drop_objection(this);
  endtask

endclass