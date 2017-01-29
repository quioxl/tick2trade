class feed_all_messages_seq extends feed_api_seq;

  `uvm_object_utils(feed_all_messages_seq)

  function new(string name = "feed_all_messages_seq");
    super.new(name);
  endfunction : new
  
  symbol_mapper mapper = symbol_mapper::get_mapper();

  virtual function void randomize_feed_msg(feed_message_item feed_h);
    if (!feed_h.randomize() with
          {symbol_id == mapper.find_random_symbol();}) begin
      `uvm_fatal("SEQ","Transaction randomization failed")
    end
    //`uvm_info("FEED_ALL_MESSAGE_SEQ", $sformatf("Symbol used: 16'h%04x", feed_h.symbol_id), UVM_MEDIUM)
  endfunction : randomize_feed_msg
  

endclass : feed_all_messages_seq