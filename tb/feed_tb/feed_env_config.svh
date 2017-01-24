class feed_env_config extends uvm_object;
  `uvm_object_utils(feed_env_config)

  avalon_config master_cfg_h;
  avalon_config slave_cfg_h;

  function new(string name="feed_env_config");
    super.new(name);
    master_cfg_h = avalon_config::type_id::create("master_cfg_h");
    master_cfg_h.master_slave = AVL_MASTER;
    slave_cfg_h = avalon_config::type_id::create("slave_cfg_h");
    slave_cfg_h.master_slave = AVL_SLAVE;
  endfunction

  task wait_for_reset();
    wait(master_cfg_h.vif.reset_n == 1'b1);
  endtask

  static function feed_env_config get_config (uvm_component comp, string name = "feed_env_config");
    feed_env_config cfg_h;
    if (!uvm_config_db#(feed_env_config)::get(comp,"",name,cfg_h)) begin
      comp.uvm_report_error("CFG",$sformatf("Cannot get() config %s from uvm_config_db. Hvae you set() it?",name),,`__FILE__,`__LINE__);
      return null;
    end
    return cfg_h;
  endfunction

endclass

