class all_messages_test extends system_test_base;
  `uvm_component_utils(all_messages_test)

  function new(string name = "all_messages_test", uvm_component parent = null);
    super.new(name,parent);
  endfunction : new

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    //Turn off the new order generator to prevent the RAM from changing
    cfg_h.enable_new_order_gen = 0;  //FIXME
    cfg_h.order_cfg_h.stall_frequency = 0;
  endfunction : build_phase

  virtual task run_phase(uvm_phase phase);
    random_host_program_seq host_seq_h;
    feed_all_messages_seq feed_seq_h;
    
    super.run_phase(phase);
    host_seq_h = random_host_program_seq::type_id::create("host_seq_h");
    //Program 100 symbols
    host_seq_h.trans_count = 100;
    symbols_programmed = host_seq_h.trans_count;
    `uvm_info("MESSAGES", $sformatf("%0d symbols will be programmed in strategy RAM", host_seq_h.trans_count), UVM_LOW)
    host_seq_h.start(env_h.host_agent_h.seqr_h);
    feed_seq_h = feed_all_messages_seq::type_id::create("feed_seq_h");
    `uvm_info("MESSAGES", $sformatf("%0d messages will be sent", feed_seq_h.message_count), UVM_LOW)
    messege_sent_count += feed_seq_h.message_count;
    feed_seq_h.start(env_h.layering_h.feed_message_seqr_h);
    #1us;
    phase.drop_objection(this);
  endtask : run_phase

endclass : all_messages_test