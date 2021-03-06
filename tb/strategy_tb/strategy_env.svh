class strategy_env extends uvm_env;

  `uvm_component_utils(strategy_env)

  strategy_env_config cfg_h;
  avalon_agent master_agent_h;
  host_agent   host_agent_h;
  order_agent  order_agent_h;
  strategy_predictor  predictor_h;
  strategy_scoreboard scoreboard_h;
  new_order_generator new_order_gen_h;
  strategy_coverage   coverage_h;

  function new(string name, uvm_component parent);
    super.new(name,parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    if (cfg_h == null) begin
      cfg_h = strategy_env_config::get_config(this);
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

    //Create the analysis components
    predictor_h = strategy_predictor::type_id::create("predictor_h",this);
    predictor_h.enable_new_order_gen = cfg_h.enable_new_order_gen;
    scoreboard_h = strategy_scoreboard::type_id::create("scoreboard_h",this);
    if (cfg_h.enable_new_order_gen)
      new_order_gen_h = new_order_generator::type_id::create("new_order_gen_h",this);
    coverage_h = strategy_coverage::type_id::create("coverage_h", this);
  endfunction

  virtual function void connect_phase(uvm_phase phase);
    scoreboard_h.enable_sb = cfg_h.enable_sb;

    //Connect the master agent and the host agent to the predictor
    master_agent_h.ap.connect(predictor_h.analysis_export);
    host_agent_h.mon_out_ap.connect(predictor_h.host_export);
    //Connect the predictor and the order agent to the scoreboard
    predictor_h.ap.connect(scoreboard_h.expect_ai);
    order_agent_h.ap.connect(scoreboard_h.actual_ai);

    if (cfg_h.enable_new_order_gen) begin
      new_order_gen_h.host_seqr_h = host_agent_h.seqr_h;
      order_agent_h.ap.connect(new_order_gen_h.analysis_export);
    end

    //Connect Coverage Collector
    master_agent_h.ap.connect(coverage_h.feed_export);
    host_agent_h.mon_out_ap.connect(coverage_h.host_export);
    order_agent_h.ap.connect(coverage_h.order_export);
    
  endfunction

endclass



