class strategy_env_config extends uvm_object;
  `uvm_object_utils(strategy_env_config)

  avalon_config master_cfg_h;
  host_config   host_cfg_h;
  order_config  order_cfg_h;

  bit enable_sb = 1;
  bit enable_new_order_gen = 1;

  function new(string name="strategy_env_config");
    super.new(name);
    master_cfg_h = avalon_config::type_id::create("master_cfg_h");
    master_cfg_h.master_slave = AVL_MASTER;
    host_cfg_h   = host_config::type_id::create("host_cfg_h");
    order_cfg_h  = order_config::type_id::create("host_cfg_h");
  endfunction

  task wait_for_reset();
    wait(master_cfg_h.vif.reset_n == 1'b1);
  endtask

  task wait_for_clocks(int count = 1);
    repeat (count) @(posedge master_cfg_h.vif.clk);
  endtask

  task wait_for_reset_host();
    wait(host_cfg_h.host_intf.reset_n == 1'b1);
  endtask

  task wait_for_clocks_host(int count = 1);
    repeat (count) @(posedge host_cfg_h.host_intf.clk);
  endtask

  static function strategy_env_config get_config (uvm_component comp, string name = "strategy_env_config");
    strategy_env_config cfg_h;
    if (!uvm_config_db#(strategy_env_config)::get(comp,"",name,cfg_h)) begin
      comp.uvm_report_error("CFG",$sformatf("Cannot get() config %s from uvm_config_db. Have you set() it?",name),,`__FILE__,`__LINE__);
      return null;
    end
    return cfg_h;
  endfunction

endclass : strategy_env_config

