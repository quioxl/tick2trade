class feed_predictor extends uvm_subscriber #(avalon_seq_item_base);
  `uvm_component_utils(feed_predictor)

  function new(string name, uvm_component parent);
    super.new(name,parent);
  endfunction

  feed_message_item feed_trans_h;
  uvm_analysis_port #(feed_message_item) ap;

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    ap = new("ap",this);
  endfunction

  function void write(avalon_seq_item_base t);
    if (t.payload.size() != 17) begin
      return;
    end
    feed_trans_h = feed_message_item::type_id::create("feed_trans_h");
    feed_trans_h.payload = t.payload;
    feed_trans_h.msg_unpack();
    if (feed_trans_h.msg_type != "NEW") begin
      return;
    end
    ap.write(feed_trans_h);
  endfunction

endclass