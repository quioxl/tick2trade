class mixed_message_test extends feed_test_base;
  `uvm_component_utils(mixed_message_test)

  function new(string name = "mixed_message_test", uvm_component parent = null);
    super.new(name,parent);
  endfunction

  virtual task run_phase(uvm_phase phase);
    feed_api_seq seq_h;
    super.run_phase(phase);
    seq_h = feed_api_seq::type_id::create("seq_h");
    seq_h.start(seqr_h);
    #10us;
    phase.drop_objection(this);
  endtask

endclass