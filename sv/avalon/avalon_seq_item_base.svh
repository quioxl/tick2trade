class avalon_seq_item_base extends uvm_sequence_item;

  `uvm_object_utils(avalon_seq_item_base)

  rand bit [7:0] payload [];
  rand int delay_gap;

  bit send_now = 0;

  function new(string name = "avalon_message_seq_item");
    super.new(name);
  endfunction

  constraint length_c { payload.size <= 1500; payload.size > 0; }
  constraint delay_gap_c { delay_gap >= 0; delay_gap <= 25; }

  virtual function string convert2string();
    return $sformatf("Size : %0d bytes",payload.size());
  endfunction

  virtual function void do_print(uvm_printer printer);
    if (printer.knobs.sprint == 0) begin
      $display(convert2string());
    end else begin
      printer.m_string = convert2string();
    end
  endfunction

  virtual function bit do_compare(uvm_object rhs, uvm_comparer comparer);
    avalon_seq_item_base rhs_;
    if (!$cast(rhs_,rhs)) return 0;
    return (super.do_compare(rhs,comparer) && (payload == rhs_.payload));
  endfunction

  virtual function void do_copy(uvm_object rhs);
    avalon_seq_item_base rhs_;
    if (!$cast(rhs_,rhs)) begin
      `uvm_fatal("ITEM","Cast failed in do_copy()")
    end
    super.do_copy(rhs);
    payload = rhs_.payload;
    delay_gap = rhs_.delay_gap;
    send_now = rhs_.send_now;
  endfunction

  virtual function void msg_pack();
  endfunction

  virtual function void msg_unpack();
  endfunction

endclass