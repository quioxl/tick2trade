class feed_streaming_monitor extends uvm_component;
  `uvm_component_utils(feed_streaming_monitor)

  function new(string name, uvm_component parent);
    super.new(name,parent);
  endfunction

  avalon_message_item trans_h;
  uvm_analysis_port #(avalon_message_item) ap;
  avalon_config cfg_h;

  virtual avalon_if vif;

  function void build_phase(uvm_phase phase);
    ap = new("ap",this);
    if (cfg_h == null) begin
      `uvm_fatal("MON","cfg_h uninitialized")
    end
  endfunction

  function void connect_phase(uvm_phase phase);
    vif = cfg_h.vif;
  endfunction

  virtual function void push_beat(ref bit [7:0] p [$]);
    bit [63:0] beat_data = vif.data;
    repeat (8) begin
      p.push_back(beat_data[63:56]);
      beat_data = beat_data << 8;
    end
  endfunction

  virtual task accum_beat(ref bit [7:0] p [$]);
    @(posedge vif.clk);
    while (vif.valid !== 1'b1) @(posedge vif.clk);
    push_beat(p);
  endtask

  virtual function void build_trans(ref bit [7:0] p [$],bit [15:0] msg_length);
    bit [7:0] full_msg [$];
    trans_h = avalon_message_item::type_id::create("trans_h");
    repeat (msg_length) begin
      full_msg.push_back(p.pop_front());
    end
    trans_h.payload = full_msg;
    ap.write(trans_h);
  endfunction

  virtual task run_phase(uvm_phase phase);
    bit [7:0] p [$];
    bit [63:0] beat_data;
    bit [15:0] msg_count = 0;
    bit [15:0] msg_length = 0;
    cfg_h.wait_for_reset();
    forever begin
      @(posedge vif.clk);
      while (vif.valid !== 1'b1 || vif.startofpacket !== 1'b1) begin
        @(posedge vif.clk);
      end
      // If we got here, we're inside of a new packet. Push what we have to 
      // start onto the queue
      push_beat(p);
      // First beat has the message count in it, pull that out
      msg_count[15:8] = p.pop_front();
      msg_count[7:0] = p.pop_front();
      // Loop on the following until we run out of messages to parse
      while (msg_count > 0) begin
        // First we need the message length. If we don't have enough data (2 bytes) in
        // the queue, accumulate another beat. Otherwise, pull that out
        if (p.size() < 2) begin
          accum_beat(p);
        end
        msg_length[15:8] = p.pop_front();
        msg_length[7:0] = p.pop_front();
        // Now grab enough data to fill out the current message
        while (p.size() < msg_length) begin
          accum_beat(p);
        end
        // With enough data, we can now populate and send a new transaction
        build_trans(p,msg_length);
        // Decrement message count
        msg_count--;
      end
      // At this point, the only things left in the queue should be throwaway bits
      // in number equal to what is now on the "empty" field, and EOP should
      // be asserted.  If it isn't, throw an error just to be helpful.
      if (p.size() !== vif.empty) begin
        `uvm_error("MON",$sformatf("Mismatch between queue remainder (%0d) and empty field (%0d)",p.size(),vif.empty))
      end
      if (vif.endofpacket !== 1'b1) begin
        `uvm_error("MON","EOP not asserted at expected time");
      end
      p = {};
    end
  endtask

endclass