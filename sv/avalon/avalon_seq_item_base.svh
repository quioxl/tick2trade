// Sequence item definition for Avalon protocol

class avalon_seq_item_base extends uvm_sequence_item;

  `uvm_object_utils(avalon_seq_item_base)

  // Payload is on byte boundary, fully randomized
  rand bit [7:0] payload [];
  // Gap between this transaction and the next is controlled by this random variable
  rand int delay_gap;

  // Set this bit to tell the driver to send the data immediately instead of
  // accumulating the data in a larger packet
  bit send_now = 0;

  function new(string name = "avalon_message_seq_item");
    super.new(name);
  endfunction

  // Random constraints. Payload must be larger than zero but smaller than 1500 bytes
  constraint length_c { payload.size <= 1500; payload.size > 0; }
  // Keep the delay under 25 cycles
  constraint delay_gap_c { delay_gap >= 0; delay_gap <= 25; }

  // Return informational string for debug - only provide size info (data would just be spammy)
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

  // Comparison function - return 1 if this object contents matches that of the passed in object
  virtual function bit do_compare(uvm_object rhs, uvm_comparer comparer);
    avalon_seq_item_base rhs_;
    if (!$cast(rhs_,rhs)) return 0;
    return (super.do_compare(rhs,comparer) && (payload == rhs_.payload));
  endfunction

  // Copy function - initializes local members to match that of the passed in object
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

  // Empty pack/unpack functions, intended for use in extended classes
  virtual function void msg_pack();
  endfunction

  virtual function void msg_unpack();
  endfunction

endclass