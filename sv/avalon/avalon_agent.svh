// This is the top-level component wrapper for the Avalon protocol agent.
// By default it will be active, i.e. instantiate a driver and sequencer.
// The driver instantiated depends on a configuration variable toggling
// between master/slave mode of operation.
// A parallel monitor component snoops the avalon bus and sends transactional
// data out to an analysis port
class avalon_agent extends uvm_agent;

  `uvm_component_utils(avalon_agent)

  avalon_config cfg_h;
  avalon_driver_base driver_h;
  avalon_monitor monitor_h;
  uvm_sequencer #(avalon_seq_item_base) seqr_h;

  avalon_coverage cov_h;
  
  uvm_analysis_port #(avalon_seq_item_base) ap;

  function new(string name, uvm_component parent);
    super.new(name,parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    if (cfg_h == null) begin
      cfg_h = avalon_config::get_config(this);
    end
    if (cfg_h == null)
      `uvm_fatal("DRV","Failed to pull cfg_h from config_db")
    if (cfg_h.active == UVM_ACTIVE) begin
      if (cfg_h.master_slave == AVL_MASTER) begin
        driver_h = avalon_master_driver::type_id::create("driver_h",this);
      end else begin
        driver_h = avalon_slave_driver::type_id::create("driver_h",this);
      end
      driver_h.cfg_h = cfg_h;
      seqr_h = new("seqr_h",this);
    end
    cov_h = avalon_coverage::type_id::create("cov_h",this);
    monitor_h = avalon_monitor::type_id::create("monitor_h",this);
    monitor_h.cfg_h = cfg_h;
    ap = new("ap",this);
  endfunction

  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    if (cfg_h.active == UVM_ACTIVE) begin
      driver_h.seq_item_port.connect(seqr_h.seq_item_export);
    end
    monitor_h.ap.connect(ap);
    monitor_h.ap.connect(cov_h.analysis_export);
  endfunction

endclass