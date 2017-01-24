class feed_message_to_avalon_seq extends uvm_sequence #(avalon_seq_item_base);

  `uvm_object_utils(feed_message_to_avalon_seq)

  uvm_sequencer #(avalon_seq_item_base) up_seqr;

  rand int next_down_size;
  bit [7:0] accum_payload [$];
  bit [15:0] message_count;

  constraint down_size_c { next_down_size >= 8; next_down_size <= 1500; }

  function new(string name = "feed_message_to_avalon_seq");
    super.new(name);
  endfunction

  virtual task body();
    avalon_seq_item_base up_trans_h;
    avalon_seq_item_base down_trans_h;
    bit [15:0] msg_size;
    forever begin
      up_seqr.get_next_item(up_trans_h);
      up_trans_h.msg_pack();
      if (!this.randomize()) begin
        `uvm_fatal("SEQ","Randomization failed")
      end
      // If the transaction we just got indicated for it to be sent immediately, do so
      if (up_trans_h.send_now == 1'b1) begin
        // First, flush whatever we've accumulated to maintain in-order delivery
        if (accum_payload.size() > 0) begin
          down_trans_h = avalon_seq_item_base::type_id::create();
          start_item(down_trans_h);
          build_packet(down_trans_h);
          finish_item(down_trans_h);
        end
        // Then send the current transaction
        down_trans_h = avalon_seq_item_base::type_id::create();
        start_item(down_trans_h);
        msg_size = up_trans_h.payload.size();
        accum_payload = up_trans_h.payload;
        accum_payload.push_front(msg_size[7:0]);
        accum_payload.push_front(msg_size[15:8]);
        message_count = 1;
        build_packet(down_trans_h);
        finish_item(down_trans_h);
      end else begin
        // Otherwise, check to see if what we just got plus what we've accumulated would be too
        // large.  If so, send what we've accumulated
        if (up_trans_h.payload.size() + 4 + accum_payload.size() >= next_down_size) begin
          down_trans_h = avalon_seq_item_base::type_id::create();
          start_item(down_trans_h);
          build_packet(down_trans_h);
          finish_item(down_trans_h);
        end
        // Add what we just got to the end of the accumulated payload
        msg_size = up_trans_h.payload.size();
        accum_payload.push_back(msg_size[15:8]);
        accum_payload.push_back(msg_size[7:0]);
        foreach (up_trans_h.payload[i]) begin
          accum_payload.push_back(up_trans_h.payload[i]);
        end
        // Update the message count at the front of the downstream payload
        message_count++;
      end
      up_seqr.item_done();
    end
  endtask

  virtual function void build_packet(avalon_seq_item_base target_h);
    if (!target_h.randomize()) begin
      // We're doing this to randomize delay between packets
      `uvm_fatal("SEQ","Item randomization failed")
    end
    accum_payload.push_front(message_count[7:0]);
    accum_payload.push_front(message_count[15:8]);
    target_h.payload = accum_payload;
    message_count = 0;
    accum_payload = {};
    if (!this.randomize()) begin
      `uvm_fatal("SEQ","Self-randomization failed")
    end
  endfunction

endclass