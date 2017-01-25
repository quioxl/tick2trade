//////////////////////////////////////////////////////////////////////////////
// host_monitor - a monitor to connect the interface to the analysis group
//////////////////////////////////////////////////////////////////////////////
class host_monitor extends uvm_monitor;

  //Register with the Factory
  `uvm_component_utils(host_monitor)

  //Analysis Port(s)
  uvm_analysis_port #(host_item)    result_from_monitor_ap;

  //Virtual Interface(s)
  virtual      host_interface       host_interface_h;

  //Variables
  const string report_id = "HOST_MONITOR";
  host_item                         transaction_h;
  host_config                       cfg_h;  //Config object handle


  function new(string name, uvm_component p);
    super.new(name, p);
    //`uvm_info(report_id, $sformatf("just built a host monitor called %s", name), UVM_LOW)
  endfunction : new

  function void build_phase(uvm_phase phase);
    //super.build_phase(phase);  //Don't call - Large Performance Impact
    
    // and add an analysis port for the host packets
    result_from_monitor_ap = new("result_from_monitor_ap", this);
  endfunction : build_phase
  
  function void connect_phase(uvm_phase phase);
    if (cfg_h == null)
      `uvm_fatal(report_id, "Agent did not push config down to Driver")
    else
      host_interface_h = cfg_h.host_intf;
  endfunction : connect_phase


  task run_phase(uvm_phase phase);
    // wait for reset to deassert...
    @(posedge host_interface_h.reset_n);
    //Go into a loop to capture the transactions and then send them out of an
    // analysis port
    forever @(posedge host_interface_h.in_config_valid) begin

      transaction_h = new("host_monitor_item");

      transaction_h.data = host_interface_h.in_config_data;

      //Could add a timeout on the accept signal
      while (host_interface_h.in_config_accept == 0)
        @(posedge host_interface_h.clk);
      
      result_from_monitor_ap.write(transaction_h);
    end // forever @(posedge host_interface_h.in_config_valid)
  endtask : run_phase

endclass : host_monitor
