// Avalon configuration object definition
// Contains variables and convenience hooks
class avalon_config extends uvm_object;
  `uvm_object_utils(avalon_config)

  // Virtual interface associated with a specific instantiation of the avalon agent
  virtual avalon_if vif;

  // Timeout value (measured in clock cycles) to be used across this agent
  int timeout = 200;

  // If active, a driver/sequencer pair will be included with the agent.  Otherwise we'll just
  // get a monitor
  uvm_active_passive_enum active = UVM_ACTIVE;
  // If MASTER, we will drive most of the signals on the interface, responding to READY.
  // If Slave, we drive READY and pull in the other signals
  avalon_master_slave_enum master_slave = AVL_MASTER;

  // How often will the slave driver inject a stall (ready=0)
  int slave_stall_frequency = 1;
  // What will the duration of that stall be (min/max clocks)
  int slave_max_stall = 5;
  int slave_min_stall = 1;

  // Convenience function (static) to provide more consistent way to pull this object from the UVM configuration db.
  static function avalon_config get_config (uvm_component comp, string name = "avalon_config");
    avalon_config cfg_h;
    if (!uvm_config_db#(avalon_config)::get(comp,"",name,cfg_h)) begin
      comp.uvm_report_error("CFG",$sformatf("Cannot get() config %s from uvm_config_db. Hvae you set() it?",name),,`__FILE__,`__LINE__);
      return null;
    end
    return cfg_h;
  endfunction

  // Blocks until reset is inactive - useful for monitors/drivers to avoid starting too early
  task wait_for_reset();
    wait(vif.reset_n === 1'b1);
  endtask

endclass