// Predictor component for use in avalon feed TLM paths
//  Often predictors will do some sort of object manipulation or filtering on
//  incoming object stream, but in this case all the predictor does is convert
//  transactions of type avalon_message_item to the base class type "avalon_seq_item_base"

// This allows the downstream scoreboard to be symmetrical, i.e. both sides act on
// the base Avalon sequence item

class feed_predictor extends uvm_subscriber #(avalon_message_item);
  `uvm_component_utils(feed_predictor)

  function new(string name, uvm_component parent);
    super.new(name,parent);
  endfunction

  avalon_seq_item_base base_trans_h;
  uvm_analysis_port #(avalon_seq_item_base) ap;

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    ap = new("ap",this);
  endfunction

  function void write(avalon_message_item t);
    base_trans_h = avalon_seq_item_base::type_id::create("feed_trans_h");
    base_trans_h.copy(t);
    ap.write(base_trans_h);
  endfunction

endclass