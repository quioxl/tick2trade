class strategy_coverage extends uvm_component;
  `uvm_component_utils(strategy_coverage)

  //TLM ports & imps
  uvm_analysis_imp_feed #(avalon_seq_item_base, strategy_coverage) feed_export;
  uvm_analysis_imp_host #(host_item,            strategy_coverage) host_export;
  uvm_analysis_imp_order #(order_item,          strategy_coverage) order_export;

  //Local handles for sampling
  avalon_seq_item_base feed_item_h;
  host_item            host_item_h;
  order_item           order_item_h;
  
  //Covergroups
  covergroup feed_items;
    SIZE: coverpoint feed_item_h.payload.size()
      {
       illegal_bins too_small = {[0:7]};
       bins         valid[]   = {[8:32]};
       illegal_bins too_large = {[33:$]};
       }
  endgroup : feed_items
  
  //Methods
  function new(string name, uvm_component parent);
    super.new(name,parent);
    feed_items = new();
  endfunction : new

  function void build_phase(uvm_phase phase);
    feed_export  = new("feed_export",this);
    host_export  = new("host_export",this);
    order_export = new("order_export",this);
  endfunction : build_phase
  
  
  function void write_feed(avalon_seq_item_base t);
    feed_item_h = t;
    feed_items.sample();
  endfunction : write_feed
  
  function void write_host(host_item t);
    host_item_h = t;
  endfunction : write_host
  
  function void write_order(order_item t);
    order_item_h = t;
  endfunction : write_order
  
endclass : strategy_coverage
