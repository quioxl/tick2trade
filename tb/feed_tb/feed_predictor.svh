class feed_predictor extends uvm_subscriber #(avalon_message_item);
  `uvm_component_utils(feed_predictor)

  function new(string name, uvm_component parent);
    super.new(name,parent);
  endfunction

  avalon_message_item feed_trans_h;
  uvm_analysis_port #(avalon_message_item) ap;

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    ap = new("ap",this);
  endfunction

  function void write(avalon_message_item t);
    feed_trans_h = avalon_message_item::type_id::create("feed_trans_h");
    feed_trans_h.copy(t);
    ap.write(feed_trans_h);
  endfunction

endclass