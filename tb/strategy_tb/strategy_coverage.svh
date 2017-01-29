class strategy_coverage extends uvm_component;
  `uvm_component_utils(strategy_coverage)

  //TLM ports & imps
  uvm_analysis_imp_feed #(avalon_seq_item_base, strategy_coverage) feed_export;
  uvm_analysis_imp_host #(host_item,            strategy_coverage) host_export;
  uvm_analysis_imp_order #(order_item,          strategy_coverage) order_export;

  //Local handles for sampling
  avalon_seq_item_base feed_item_h;
  host_trans_t         host_struct;
  order_item           order_item_h;
  
  //Covergroups
  covergroup feed_items;
    SIZE: coverpoint feed_item_h.payload.size()
      {
       illegal_bins too_small = {[0:7]};
       bins         size[]    = {[8:32]};
       illegal_bins too_large = {[33:$]};
       }
    TYPE: coverpoint {feed_item_h.payload[0], feed_item_h.payload[1], feed_item_h.payload[2]}
      {
       bins NEW = {"NEW"};
       bins others = {[0:("NEW"-1)],[("NEW"+1):24'hffffff]};
      }
    SIZE_TYPE: cross SIZE, TYPE;
  endgroup : feed_items

  covergroup host_items;
    CMDS: coverpoint host_struct.cmd;
    RAMS: coverpoint host_struct.ram;
    ADDR: coverpoint host_struct.addr iff (host_struct.ram != SYMBOL)
      //Only for not symbol because that is when the RAM address is on the line
      {
       bins low_range            = {[16'h0000:16'h0fff]};
       bins medium_range         = {[16'h1000:16'h2fff]};
       bins high_range           = {[16'h3000:16'h3fff]};
       illegal_bins out_of_range = {[16'h4000:$]};
      }
  endgroup : host_items

  covergroup order_items;
    SYMBOLS: coverpoint order_item_h.data[127:112]
      {
       bins low_range            = {[16'h0000:16'h3fff]};
       bins low_med_range        = {[16'h4000:16'h7fff]};
       bins med_high_range       = {[16'h8000:16'hbfff]};
       bins high_range           = {[16'hc000:16'hffff]};
      }
  endgroup : order_items
  
  
  //Methods
  function new(string name, uvm_component parent);
    super.new(name,parent);
    feed_items = new();
    host_items = new();
    order_items = new();
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
    host_struct = t.data;
    host_items.sample();
  endfunction : write_host
  
  function void write_order(order_item t);
    order_item_h = t;
    order_items.sample();
  endfunction : write_order
  
endclass : strategy_coverage
