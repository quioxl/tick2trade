class system_env extends uvm_env;

  `uvm_component_utils(system_env)

  //Data Members
  //Config
  system_env_config cfg_h;
  //Agents
  avalon_agent        master_agent_h;
  host_agent          host_agent_h;
  order_agent         order_agent_h;
  //Feed Layering
  feed_layering layering_h;
  feed_monitor monitor_h;
  uvm_analysis_port #(avalon_message_item) feed_ap;
  uvm_sequencer#(avalon_message_item) feed_message_seqr_h;
  //Analysis
  feed_streaming_monitor stream_mon_h;
  feed_predictor      feed_pred_h;
  strategy_predictor  strat_pred_h;
  strategy_scoreboard scoreboard_h;
  new_order_generator new_order_gen_h;

  function new(string name, uvm_component parent);
    super.new(name,parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    //Config
    if (cfg_h == null) begin
      cfg_h = system_env_config::get_config(this);
    end
    if (cfg_h == null) begin
      `uvm_fatal("ENV","Failed to pull cfg_h from config_db");
    end
    //Create the agents
    master_agent_h = avalon_agent::type_id::create("master_agent_h",this);
    master_agent_h.cfg_h = cfg_h.master_cfg_h;
    host_agent_h   = host_agent::type_id::create("host_agent_h",this);
    host_agent_h.cfg_h = cfg_h.host_cfg_h;
    order_agent_h  = order_agent::type_id::create("order_agent_h",this);
    order_agent_h.cfg_h = cfg_h.order_cfg_h;
    
    //Feed Layering
    layering_h = feed_layering::type_id::create("layering_h",this);
    monitor_h = feed_monitor::type_id::create("monitor_h",this);
    feed_ap = new("feed_ap",this);
    feed_message_seqr_h = new("feed_message_seqr_h",this);
    
    //Create the analysis components
    stream_mon_h = feed_streaming_monitor::type_id::create("stream_mon_h",this);
    stream_mon_h.cfg_h = cfg_h.master_cfg_h;
    feed_pred_h  = feed_predictor::type_id::create("feed_pred_h",this);
    strat_pred_h = strategy_predictor::type_id::create("strat_pred_h",this);
    scoreboard_h = strategy_scoreboard::type_id::create("scoreboard_h",this);
    if (cfg_h.enable_new_order_gen)
      new_order_gen_h = new_order_generator::type_id::create("new_order_gen_h",this);
  endfunction : build_phase

  virtual function void connect_phase(uvm_phase phase);
    scoreboard_h.enable_sb = cfg_h.enable_sb;

    //Connect the layering components
    layering_h.feed_message_seqr_h = feed_message_seqr_h;
    layering_h.avalon_seqr_h = master_agent_h.seqr_h;
    feed_ap.connect(monitor_h.ap);
    master_agent_h.ap.connect(monitor_h.analysis_export);
    
    //Connect the layering agent to the feed predictor
    //monitor_h.ap.connect(feed_pred_h.analysis_export);
    stream_mon_h.ap.connect(feed_pred_h.analysis_export);
    //Connect the feed predictor and the host agent to the strategy predictor
    feed_pred_h.ap.connect(strat_pred_h.analysis_export);
    host_agent_h.mon_out_ap.connect(strat_pred_h.host_export);
    //Connect the strategy predictor and the order agent to the scoreboard
    strat_pred_h.ap.connect(scoreboard_h.expect_ai);
    order_agent_h.ap.connect(scoreboard_h.actual_ai);

    if (cfg_h.enable_new_order_gen) begin
      new_order_gen_h.host_seqr_h = host_agent_h.seqr_h;
      order_agent_h.ap.connect(new_order_gen_h.analysis_export);
    end
    
  endfunction : connect_phase

endclass : system_env



