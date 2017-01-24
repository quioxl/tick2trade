class feed_env extends uvm_env;

  `uvm_component_utils(feed_env)

  feed_env_config cfg_h;
  avalon_agent master_agent_h;
  avalon_agent slave_agent_h;
  feed_layering layering_h;
  feed_monitor monitor_h;

  uvm_analysis_port #(avalon_seq_item_base) feed_ap;

  uvm_sequencer#(avalon_seq_item_base) feed_message_seqr_h;

  function new(string name, uvm_component parent);
    super.new(name,parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    if (cfg_h == null) begin
      cfg_h = feed_env_config::get_config(this);
    end
    if (cfg_h == null) begin
      `uvm_fatal("ENV","Failed to pull cfg_h from config_db");
    end
    master_agent_h = avalon_agent::type_id::create("master_agent_h",this);
    master_agent_h.cfg_h = cfg_h.master_cfg_h;
    slave_agent_h = avalon_agent::type_id::create("slave_agent_h",this);
    slave_agent_h.cfg_h = cfg_h.slave_cfg_h;
    feed_message_seqr_h = new("feed_message_seqr_h",this);
    layering_h = feed_layering::type_id::create("layering_h",this);
    monitor_h = feed_monitor::type_id::create("monitor_h",this);
    feed_ap = new("feed_ap",this);
  endfunction

  virtual function void connect_phase(uvm_phase phase);
    layering_h.feed_message_seqr_h = feed_message_seqr_h;
    layering_h.avalon_seqr_h = master_agent_h.seqr_h;
    feed_ap.connect(monitor_h.ap);
    master_agent_h.monitor_h.ap.connect(monitor_h.analysis_export);
  endfunction

endclass



