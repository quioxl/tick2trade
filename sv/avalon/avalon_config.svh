class avalon_config extends uvm_object;
  `uvm_object_utils(avalon_config)

  virtual avalon_if vif;

  uvm_active_passive_enum active = UVM_ACTIVE;
  avalon_master_slave_enum master_slave = AVL_MASTER;

  // How often will the slave driver inject a stall (ready=0)
  int slave_stall_frequency = 1;
  // What will the duration of that stall be (min/max clocks)
  int slave_max_stall = 5;
  int slave_min_stall = 1;

  static function avalon_config get_config (uvm_component comp, string name = "avalon_config");
    avalon_config cfg_h;
    if (!uvm_config_db#(avalon_config)::get(comp,"",name,cfg_h)) begin
      comp.uvm_report_error("CFG",$sformatf("Cannot get() config %s from uvm_config_db. Hvae you set() it?",name),,`__FILE__,`__LINE__);
      return null;
    end
    return cfg_h;
  endfunction

endclass