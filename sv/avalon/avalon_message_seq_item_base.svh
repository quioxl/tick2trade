class avalon_message_seq_item_base extends uvm_sequence_item;

  `uvm_object_utils(avalon_message_seq_item_base)

  rand bit [23:0] msg_type;
  rand bit [7:0] payload [];

  int message_count = 0;

  function new(string name = "avalon_message_seq_item");
    super.new(name);
  endfunction

  constraint length_c { payload.size >=5; payload.size <= 29; }

  virtual function string convert2string();
    string str;
    str = {"Size : ",payload.size(),"["};
    foreach (payload[i]) begin
      str = $sformatf("%s 0x%2h",payload[i]);
    end
    str = {str," ]"};
    return str;
  endfunction

  virtual function void do_print(uvm_printer printer);
    if (printer.knobs.sprint == 0) begin
      $display(convert2string());
    end else begin
      printer.m_string = convert2string();
    end
  endfunction

  virtual function bit do_compare(uvm_object rhs, uvm_comparer comparer);
    avalon_message_seq_item_base rhs_;
    if (!$cast(rhs_,rhs)) return 0;
    return (super.do_compare(rhs,comparer) && (payload == rhs_.payload));
  endfunction

  virtual function void do_copy(uvm_object rhs);
    avalon_message_seq_item_base rhs_;
    if (!$cast(rhs_,rhs)) begin
      `uvm_fatal("ITEM","Cast failed in do_copy()")
    end
    super.do_copy(rhs);
    payload = rhs_.payload;
  endfunction

  virtual function void msg_pack();
    if (payload.size < 3) begin
      payload = new [3];
    end
    payload[0:2] = '{msg_type[23:16],msg_type[15:8],msg_type[7:0]};
  endfunction

  virtual function void msg_unpack();
    if (payload.size < 3) begin
      `uvm_fatal("ITEM","msg_unpack failed, payload size incorrect")
    end
    msg_type = {payload[0],payload[1],payload[2]};
  endfunction

endclass