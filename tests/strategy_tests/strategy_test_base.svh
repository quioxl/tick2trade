class strategy_test_base extends uvm_test;
  `uvm_component_utils(strategy_test_base)

  strategy_env env_h;
  strategy_env_config cfg_h;
  //uvm_sequencer #(avalon_seq_item_base,avalon_seq_item_base) seqr_h;

  function new (string name = "strategy_test_base", uvm_component parent = null);
    super.new(name,parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    cfg_h = strategy_env_config::type_id::create("cfg_h");
    env_h = strategy_env::type_id::create("env_h",this);
    env_h.cfg_h = cfg_h;
    if (!uvm_config_db #(virtual avalon_if)::get(this,"","avl_master_if",cfg_h.master_cfg_h.vif))
      `uvm_fatal("TEST","Unable to find avl_master_if entry in config db")
    if (!uvm_config_db #(virtual host_interface)::get(this,"","host_if",cfg_h.host_cfg_h.host_intf))
      `uvm_fatal("TEST","Unable to find host_if entry in config db")
  endfunction

/* -----\/----- EXCLUDED -----\/-----
  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    seqr_h = env_h.layering_h.strategy_message_seqr_h;
  endfunction
 -----/\----- EXCLUDED -----/\----- */

  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
    phase.raise_objection(this);
    cfg_h.wait_for_reset();
    cfg_h.wait_for_clocks(10);
  endtask

endclass
