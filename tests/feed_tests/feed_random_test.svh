class feed_random_test extends feed_test_base;
  `uvm_component_utils(feed_random_test)

  function new(string name = "feed_random_test", uvm_component parent = null);
    super.new(name,parent);
  endfunction

  virtual task run_phase(uvm_phase phase);
    feed_random_seq seq_h;
    super.run_phase(phase);
    seq_h = feed_random_seq::type_id::create("seq_h");
    seq_h.start(seqr_h);
    #10us;
    phase.drop_objection(this);
  endtask

endclass