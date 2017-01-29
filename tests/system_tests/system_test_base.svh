class system_test_base extends uvm_test;
  `uvm_component_utils(system_test_base)

  //Data Members
  int symbols_programmed = 0;
  int message_sent_count = 0;
  
  system_env env_h;
  system_env_config cfg_h;

  function new (string name = "system_test_base", uvm_component parent = null);
    super.new(name,parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    cfg_h = system_env_config::type_id::create("cfg_h");
    env_h = system_env::type_id::create("env_h",this);
    env_h.cfg_h = cfg_h;
    if (!uvm_config_db #(virtual avalon_if)::get(this,"","feed_if",cfg_h.master_cfg_h.vif))
      `uvm_fatal("TEST","Unable to find feed_if entry in config db")
    if (!uvm_config_db #(virtual host_interface)::get(this,"","host_if",cfg_h.host_cfg_h.host_intf))
      `uvm_fatal("TEST","Unable to find host_if entry in config db")
    if (!uvm_config_db #(virtual order_interface)::get(this,"","order_if",cfg_h.order_cfg_h.vif))
      `uvm_fatal("TEST","Unable to find order_if entry in config db")
  endfunction : build_phase

  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
    phase.raise_objection(this);
    cfg_h.wait_for_reset();
    cfg_h.wait_for_clocks(10);
  endtask : run_phase

    
  function void report_phase(uvm_phase phase);
    string message;
    uvm_report_server serv = uvm_report_server::get_server();
    
    super.report_phase(phase);
    $sformat(message, "\n-------------------------------------\nSymbols Programmed  : %6d\nSymbols Reprogrammed: %6d", symbols_programmed, ((cfg_h.enable_new_order_gen) ? env_h.new_order_gen_h.symbols_reprogrammed : 0) );
    $sformat(message, "\n-------------------------------------\nSymbols Programmed  : %6d\nSymbols Reprogrammed: %6d\n-------------------------------------\nMessages Sent In            : %6d\nMessages Discarded          : %6d\nOrders Compared Successfully: %6d\nOrders Miscompared          : %6d\n-------------------------------------\n", symbols_programmed, ((cfg_h.enable_new_order_gen) ? env_h.new_order_gen_h.symbols_reprogrammed : 0), message_sent_count, env_h.strat_pred_h.discarded.sum(), env_h.scoreboard_h.compare_count, env_h.scoreboard_h.miscompare_count);
    //Total messages sent should equal the total discarded + the total number
    // of orders
    // Additionally, the total number or reprograms should equal the total
    // number of orders
    if ((serv.get_severity_count(UVM_FATAL) == 0) && 
        (serv.get_severity_count(UVM_ERROR) == 0) &&
        (env_h.scoreboard_h.miscompare_count == 0) && (message_sent_count == (env_h.strat_pred_h.discarded.sum() + env_h.scoreboard_h.compare_count)) &&
        ( (cfg_h.enable_new_order_gen) ? (env_h.new_order_gen_h.symbols_reprogrammed == env_h.scoreboard_h.compare_count) : 1) )
      $sformat(message, "%s               PASSED\n-------------------------------------", message);
    else
      $sformat(message, "%s               FAILED\n-------------------------------------", message);
    `uvm_info("TEST_STATUS", message, UVM_NONE)
  endfunction : report_phase

endclass : system_test_base
