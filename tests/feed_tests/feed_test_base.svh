class feed_test_base extends uvm_test;
  `uvm_component_utils(feed_test_base)

  feed_env env_h;
  feed_env_config cfg_h;
  uvm_sequencer #(avalon_message_item) seqr_h;

  function new (string name = "feed_test_base", uvm_component parent = null);
    super.new(name,parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    cfg_h = feed_env_config::type_id::create("cfg_h");
    env_h = feed_env::type_id::create("env_h",this);
    env_h.cfg_h = cfg_h;
    if (!uvm_config_db #(virtual avalon_if)::get(this,"","master_if",cfg_h.master_cfg_h.vif))
      `uvm_fatal("TEST","Unable to find master_if entry in config db")
    if (!uvm_config_db #(virtual avalon_if)::get(this,"","slave_if",cfg_h.slave_cfg_h.vif))
      `uvm_fatal("TEST","Unable to find slave_if entry in config db")
  endfunction

  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    seqr_h = env_h.layering_h.feed_message_seqr_h;
  endfunction

  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
    phase.raise_objection(this);
    cfg_h.wait_for_reset();
    cfg_h.wait_for_clocks(10);
  endtask

endclass
