class feed_simple_seq extends uvm_sequence #(avalon_message_item);

  `uvm_object_utils(feed_simple_seq)

  int trans_count = 5;

  function new(string name = "feed_simple_seq");
    super.new(name);
  endfunction

  task body();
    avalon_message_item feed_trans_h;
    feed_trans_h = avalon_message_item::type_id::create("feed_trans_h");
    repeat (trans_count) begin
      start_item(feed_trans_h);
      if (!feed_trans_h.randomize() with { payload.size == 17; }) begin
        `uvm_fatal("SEQ","Transaction randomization failed")
      end
      `uvm_info("SEQ",$sformatf("Sending feed message: %s",feed_trans_h.convert2string()),UVM_MEDIUM)
      finish_item(feed_trans_h);
    end
    start_item(feed_trans_h);
    if (!feed_trans_h.randomize() with { payload.size == 17; }) begin
      `uvm_fatal("SEQ","Transaction randomization failed")
    end
    `uvm_info("SEQ",$sformatf("Sending feed message: %s",feed_trans_h.convert2string()),UVM_MEDIUM)
    feed_trans_h.send_now = 1;
    finish_item(feed_trans_h);
  endtask

endclass