class feed_symbol_match_seq extends uvm_sequence #(feed_message_item);

  `uvm_object_utils(feed_symbol_match_seq)

  int trans_count = 5;
  
  symbol_mapper mapper = symbol_mapper::get_mapper();

  function new(string name = "feed_symbol_match_seq");
    super.new(name);
  endfunction

  task body();
    feed_message_item feed_trans_h;
    feed_trans_h = feed_message_item::type_id::create("feed_trans_h");
    repeat (trans_count) begin
      start_item(feed_trans_h);
      if (!feed_trans_h.randomize() with
            {symbol_id == mapper.find_random_symbol();}) begin
        `uvm_fatal("SEQ","Transaction randomization failed")
      end
      `uvm_info("SEQ",$sformatf("Sending feed message: %s",feed_trans_h.convert2string()),UVM_MEDIUM)
      finish_item(feed_trans_h);
    end
  endtask

endclass : feed_symbol_match_seq
