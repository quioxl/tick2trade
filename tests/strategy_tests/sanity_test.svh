class sanity_test extends strategy_test_base;
  `uvm_component_utils(sanity_test)

  function new(string name = "sanity_test", uvm_component parent = null);
    super.new(name,parent);
  endfunction

  virtual task run_phase(uvm_phase phase);
    //strategy_simple_seq seq_h;
    super.run_phase(phase);
    //seq_h = strategy_simple_seq::type_id::create("seq_h");
    //seq_h.start(seqr_h);
    #10us;
    phase.drop_objection(this);
  endtask

endclass