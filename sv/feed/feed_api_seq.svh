// This is a convenience sequence that will allow the production of a series
// of avalon messages (8-32 byte length).  A control variable "feed_message_freq"
// allows one to specify how often a "New" feed message (17 bytes, "NEW" in first
// three bytes) is sent across vs an unconstrained avalon message.

// "message_count" controls how many messages are produced as part of this sequence.

class feed_api_seq extends uvm_sequence #(avalon_message_item);

  `uvm_object_utils(feed_api_seq)

  function new(string name = "feed_api_seq");
    super.new(name);
  endfunction

  rand int message_count = 1000;
  int feed_message_freq = 75;

  constraint message_count_c { message_count > 0; message_count < 50; }

  task body();
    avalon_message_item msg_h;
    feed_message_item feed_h;
    msg_h = avalon_message_item::type_id::create("msg_h");
    feed_h = feed_message_item::type_id::create("feed_h");
    for (int ii = 0; ii < message_count; ii++) begin
      start_item(msg_h);
      randcase
        feed_message_freq : begin
          randomize_feed_msg(feed_h);
          msg_h.copy(feed_h);
        end
        (100-feed_message_freq) : begin
          if (!msg_h.randomize()) begin
            `uvm_fatal("SEQ","Randomization of msg_h failed")
          end
        end
      endcase // randcase
      if (ii == message_count - 1)
        msg_h.send_now = 1;
      finish_item(msg_h);
    end
  endtask

  virtual function void randomize_feed_msg(feed_message_item feed_h);
    if (!feed_h.randomize()) begin
      `uvm_fatal("SEQ","Randomization of feed_h failed")
    end
  endfunction

endclass




