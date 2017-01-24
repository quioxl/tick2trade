class avalon_message_seq_item_new extends avalon_message_seq_item_base;
  `uvm_object_utils(avalon_message_seq_item_new)

  rand bit [15:0] symbol_id;
  rand bit [63:0] price;
  rand bit [31:0] volume;

  constraint msg_type_c { msg_type == 24'h4E4557; }
  constraint symbol_id_c { symbol_id[15:14] == 2'b00; }

  function new(string name = "avalon_message_seq_item_new");
    super.new(name);
  endfunction

  virtual function string convert2string();
    return $sformatf("Type:NEW ID:0x%2h PRICE:0x%16x VOL:0x%4x",symbol_id,price,volume);
  endfunction

  virtual function bit do_compare(uvm_object rhs, uvm_comparer comparer);
    avalon_message_seq_item_new rhs_;
    if (!$cast(rhs_,rhs)) return 0;
    rhs_.msg_pack();
    return super.do_compare(rhs,comparer);
  endfunction

  virtual function void do_copy(uvm_object rhs);
    avalon_message_seq_item_new rhs_;
    if (!$cast(rhs_,rhs)) begin
      `uvm_fatal("ITEM","Cast failed in do_copy()")
    end
    rhs_.msg_pack();
    super.do_copy(rhs);
    rhs_.msg_unpack();
  endfunction

  virtual function void msg_pack();
    payload = new [17];
    super.msg_pack();
    payload[3:4] = '{symbol_id[15:8],symbol_id[7:0]};
    payload[5:12] = '{price[63:56],price[55:48],price[47:40],price[39:32],
                      price[31:24],price[23:16],price[15:8],price[7:0]};
    payload[13:16] = '{volume[31:24],volume[23:16],volume[15:8],volume[7:0]};
  endfunction

  virtual function void msg_unpack();
    if (payload.size() != 17) begin
      `uvm_fatal("ITEM","msg_unpack failed, payload size incorrect")
    end
    super.msg_unpack();
    symbol_id = {payload[3],payload[4]};
    price = {payload[5],payload[6],payload[7],payload[8],payload[9],payload[10],payload[11],payload[12]};
    volume = {payload[13],payload[14],payload[15],payload[16]};
  endfunction

endclass




