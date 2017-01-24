class feed_monitor extends uvm_subscriber #(avalon_seq_item_base);
  `uvm_component_utils(feed_monitor)

  function new(string name, uvm_component parent);
    super.new(name,parent);
  endfunction

  avalon_seq_item_base feed_trans_h;

  uvm_analysis_port #(avalon_seq_item_base) ap;

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    ap = new("ap",this);
  endfunction

  function void write(avalon_seq_item_base t);
    bit [15:0] msg_count;
    bit [15:0] msg_length;
    bit [7:0] payload [$];
    bit [7:0] msg [$];
    payload = t.payload;
    // We are receiving Avalon transactions that are (hopefully) 
    // formatted to contain feed messages.  The first two bytes
    // is the message count.
    msg_count[15:8] = payload.pop_front();
    msg_count[7:0] = payload.pop_front();
    repeat (msg_count) begin
      // Each message is predicated by a message length. Pull that out.
      msg_length[15:8] = payload.pop_front();
      msg_length[7:0] = payload.pop_front();
      repeat (msg_length) begin
        msg.push_back(payload.pop_front());
      end
      // Send each individual message out on the analysis port. These
      // will be of type avalon_seq_item_base (not feed messages) because
      // they may be of arbitrary size.  It'll be up to a predictor
      // to filter out the messages that can make it through the DUT
      feed_trans_h = avalon_seq_item_base::type_id::create("feed_trans_h");
      feed_trans_h.payload = msg;
      `uvm_info("MON",$sformatf("Saw message: %s",feed_trans_h.convert2string()),UVM_MEDIUM)
      ap.write(feed_trans_h);
      msg = {};
    end
    // We should be at the end of the payload (nothing left)
    if (payload.size() > 0) begin
      `uvm_error("MON","Malformed packet for feed data")
    end
  endfunction    

endclass