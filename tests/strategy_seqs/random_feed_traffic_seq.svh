class random_feed_traffic_seq extends uvm_sequence #(feed_message_item);

  `uvm_object_utils(random_feed_traffic_seq)

  int trans_count = 5;

  function new(string name = "random_feed_traffic_seq");
    super.new(name);
  endfunction

  task body();
    feed_message_item feed_trans_h;
    feed_trans_h = feed_message_item::type_id::create("feed_trans_h");
    repeat (trans_count) begin
      start_item(feed_trans_h);
      if (!feed_trans_h.randomize()) begin
        `uvm_fatal("SEQ","Transaction randomization failed")
      end
      `uvm_info("SEQ",$sformatf("Sending feed message: %s",feed_trans_h.convert2string()),UVM_MEDIUM)
      //feed_trans_h.msg_pack();
      finish_item(feed_trans_h);
    end
  endtask

endclass : random_feed_traffic_seq
