////////////////////////////////////////////////////////////////////////////
// host_agent - The host agent which contains the driver, sequencer and
//           monitor
////////////////////////////////////////////////////////////////////////////
class host_agent extends uvm_agent;

  //Register with the Factory
  `uvm_component_utils(host_agent)

  const string report_id = "HOST_AGENT";

  host_driver                           m_driver;
  uvm_sequencer #(host_item, host_item) m_sequencer;
  host_monitor                          m_monitor;
  uvm_analysis_port #(host_item)        m_mon_out_ap;

  host_config                           m_host_cfg;  //Config object handle

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction // new

  function void build_phase(uvm_phase phase);
    //super.build_phase(phase);  //Don't call - Large Performance Impact
    //Get the config object
    if (!uvm_config_db #(host_config)::get(this, "", 
                               "host_config", m_host_cfg))
      `uvm_fatal(report_id, "Cannot get() configuration host_config from uvm_config_db. Have you set() it?")

    //Build the driver and controller
    if (m_host_cfg.active) begin
      //`uvm_info(report_id, "Getting Driver from Factory", UVM_LOW )
      m_driver   = host_driver::type_id::create("m_driver", this);
      //`uvm_info(report_id, "Newing host sequencer", UVM_LOW )
      m_sequencer = new("m_sequencer", this);
      //Place the sequencer into the resource database for sequences to use
      //uvm_config_db #(uvm_sequencer #(host_item, host_item))::set(null,"*","host_sequencer",m_sequencer);
    end

    //`uvm_info(report_id, "Getting Monitor from the Factory", UVM_LOW )
    m_monitor  = host_monitor::type_id::create("m_monitor", this);
    // new the analysis port
    m_mon_out_ap = new("m_mon_out_ap", this);

  endfunction : build_phase

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    // connect up the uvm ports
    if (m_host_cfg.active) begin
      //Push the config down into the driver
      m_driver.host_cfg_h = m_host_cfg;
      //Connect the driver's port
      m_driver.seq_item_port.connect(m_sequencer.seq_item_export);
    end
    //Push the config down into the monitor
    m_monitor.host_cfg_h = m_host_cfg;
    // connect the analysis port in the monitor to the agent port
    m_monitor.result_from_monitor_ap.connect(m_mon_out_ap);
  endfunction : connect_phase

endclass : host_agent
