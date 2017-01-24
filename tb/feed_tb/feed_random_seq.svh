class feed_simple_seq extends uvm_sequence #(avalon_seq_item_base);

  `uvm_object_utils(feed_simple_seq)

  int trans_count = 1000;

  function new(string name = "feed_simple_seq");
    super.new(name);
  endfunction

  task body();
    feed_message_item feed_trans_h;
    avalon_seq_item_base avalon_trans_h, copy_h;
    feed_trans_h = feed_message_item::type_id::create("feed_trans_h");
    avalon_trans_h = avalon_seq_item_base::type_id::create("avalon_trans_h");
    repeat (trans_count) begin
      start_item(avalon_trans_h);
      if (!feed_trans_h.randomize()) begin
        `uvm_fatal("SEQ","Transaction randomization failed")
      end
      `uvm_info("SEQ",$sformatf("Sending feed message: %s",trans_h.convert2string()),UVM_MEDIUM)
      feed_trans_h.msg_pack();
      avalon_trans_h.copy(feed_trans_h);
      finish_item(avalon_trans_h);
    end
  endtask

endclass