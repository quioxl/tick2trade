class order_agent extends uvm_agent;
  `uvm_component_utils(order_agent)

  uvm_analysis_port #(order_item) ap;
  order_driver driver_h;
  order_monitor monitor_h;
  order_config cfg_h;

  function new (string name, uvm_component parent);
    super.new(name,parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    if (cfg_h == null) begin
      cfg_h = order_config::get_config(this);
    end
    if (cfg_h == null) begin
      `uvm_fatal("AGT","Unable to retrieve config from db")
    end
    if (cfg_h.active_passive == UVM_ACTIVE) begin
      driver_h = order_driver::type_id::create("driver_h",this);
      driver_h.cfg_h = cfg_h;
    end 
    monitor_h = order_monitor::type_id::create("monitor_h",this);
    monitor_h.cfg_h = cfg_h;
  endfunction

  virtual function void connect_phase(uvm_phase phase);
    monitor_h.ap.connect(ap);
  endfunction

endclass