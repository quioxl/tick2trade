class feed_api_seq extends uvm_sequence #(avalon_message_item);

  `uvm_object_utils(feed_api_seq)

  function new(string name = "feed_api_seq");
    super.new(name);
  endfunction

  rand int message_count;
  int feed_message_freq = 75;

  constraint message_count_c { message_count > 0; message_count < 50; }

  task body();
    avalon_message_item msg_h;
    feed_message_item feed_h;
    msg_h = avalon_message_item::type_id::create("msg_h");
    feed_h = feed_message_item::type_id::create("feed_h");
    repeat (message_count) begin
      randcase
        feed_message_freq : begin
        end
      endcase
    end
  endtask

endclass




