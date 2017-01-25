////////////////////////////////////////////////////////////////////////////
// host_agent - The host agent which contains the driver, sequencer and
//           monitor
////////////////////////////////////////////////////////////////////////////
class host_agent extends uvm_agent;

  //Register with the Factory
  `uvm_component_utils(host_agent)

  const string report_id = "HOST_AGENT";

  host_driver                           driver_h;
  uvm_sequencer #(host_item, host_item) sequencer_h;
  host_monitor                          monitor_h;
  uvm_analysis_port #(host_item)        mon_out_ap;

  host_config                           cfg_h;  //Config object handle

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction // new

  function void build_phase(uvm_phase phase);
    //super.build_phase(phase);  //Don't call - Large Performance Impact
    if (cfg_h == null) 
      //Get the config object
      if (!uvm_config_db #(host_config)::get(this, "", 
                                             "host_config", cfg_h))
        `uvm_fatal(report_id, "Cannot get() configuration host_config from uvm_config_db. Have you set() it?")

    //Build the driver and controller
    if (cfg_h.active) begin
      //`uvm_info(report_id, "Getting Driver from Factory", UVM_LOW )
      driver_h   = host_driver::type_id::create("driver_h", this);
      //Push the config down into the driver
      driver_h.cfg_h = cfg_h;
      //`uvm_info(report_id, "Newing host sequencer", UVM_LOW )
      sequencer_h = new("sequencer_h", this);
      //Place the sequencer into the resource database for sequences to use
      //uvm_config_db #(uvm_sequencer #(host_item, host_item))::set(null,"*","host_sequencer",m_sequencer);
    end

    //`uvm_info(report_id, "Getting Monitor from the Factory", UVM_LOW )
    monitor_h  = host_monitor::type_id::create("monitor_h", this);
    //Push the config down into the monitor
    monitor_h.cfg_h = cfg_h;
    // new the analysis port
    mon_out_ap = new("mon_out_ap", this);

  endfunction : build_phase

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    // connect up the uvm ports
    if (cfg_h.active) begin
      //Connect the driver's port
      driver_h.seq_item_port.connect(sequencer_h.seq_item_export);
    end
    // connect the analysis port in the monitor to the agent port
    monitor_h.result_from_monitor_ap.connect(mon_out_ap);
  endfunction : connect_phase

endclass : host_agent
