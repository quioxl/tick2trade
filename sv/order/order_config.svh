class order_config extends uvm_object;
  `uvm_object_utils(order_config)

  int stall_frequency = 1;
  int max_stall_width = 10;
  int min_stall_width = 1;

  uvm_active_passive_enum active_passive = UVM_ACTIVE;

  virtual order_interface vif;

  static function order_config get_config (uvm_component comp, string name = "order_config");
    order_config cfg_h;
    if (!uvm_config_db#(order_config)::get(comp,"",name,cfg_h)) begin
      comp.uvm_report_error("CFG",$sformatf("Cannot get() config %s from uvm_config_db",name));
      return null;
    end
    return cfg_h;
  endfunction
  
  task wait_for_reset();
    wait(vif.reset_n == 1'b1);
  endtask

endclass
