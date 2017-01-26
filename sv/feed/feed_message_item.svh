class feed_message_item extends avalon_seq_item_base;
  `uvm_object_utils(feed_message_item)

  rand bit [23:0] msg_type;
  rand bit [15:0] symbol_id;
  rand bit [63:0] price;
  rand bit [31:0] volume;

  function new(string name = "feed_message_item");
    super.new(name);
  endfunction

  constraint msg_type_c  { soft msg_type == 24'h4E4557; }

  virtual function string convert2string();
    return $sformatf("Type:%s ID:0x%2h Price:0x%8h Vol:0x%4h",msg_type,symbol_id,price,volume);
  endfunction

  virtual function void do_print(uvm_printer printer);
    if (printer.knobs.sprint == 0) begin
      $display(convert2string());
    end else begin
      printer.m_string = convert2string();
    end
  endfunction

  virtual function bit do_compare(uvm_object rhs, uvm_comparer comparer);
    feed_message_item rhs_;
    if (!$cast(rhs_,rhs)) return 0;
    return (super.do_compare(rhs,comparer) && 
            (msg_type == rhs_.msg_type) &&
            (symbol_id == rhs_.symbol_id) &&
            (price == rhs_.price) &&
            (volume == rhs_.volume));
  endfunction

  virtual function void do_copy(uvm_object rhs);
    feed_message_item rhs_;
    if (!$cast(rhs_,rhs)) begin
      `uvm_fatal("ITEM","Cast failed in do_copy()")
    end
    super.do_copy(rhs);
    msg_type = rhs_.msg_type;
    symbol_id = rhs_.symbol_id;
    price = rhs_.price;
    volume = rhs_.volume;
  endfunction

  function void post_randomize();
    msg_pack();
  endfunction

  virtual function void msg_pack();
    payload = new[17];
    payload[0] = msg_type[23:16];
    payload[1] = msg_type[15:8];
    payload[2] = msg_type[7:0];
    payload[3] = symbol_id[15:8];
    payload[4] = symbol_id[7:0];
    payload[5] = price[63:56];
    payload[6] = price[55:48];
    payload[7] = price[47:40];
    payload[8] = price[39:32];
    payload[9] = price[31:24];
    payload[10]= price[23:16];
    payload[11]= price[15:8];
    payload[12]= price[7:0];
    payload[13]= volume[31:24];
    payload[14]= volume[23:16];
    payload[15]= volume[15:8];
    payload[16]= volume[7:0];
  endfunction

  virtual function void msg_unpack();
    if (payload.size() != 17) begin
      `uvm_fatal("ITEM",$sformatf("msg_unpack: size of payload (%0d bytes) incorrect for unpack",payload.size()))
    end
    msg_type = { payload[0], payload[1], payload[2]};
    symbol_id = { payload[3], payload[4] };
    price = { payload[5], payload[6], payload[7], payload[8], payload[9], payload[10], payload[11], payload[12]};
    volume = { payload[13], payload[14], payload[15], payload[16]};
  endfunction  

endclass