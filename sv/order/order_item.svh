class order_item extends uvm_sequence_item;
  `uvm_object_utils(order_item)

  rand bit [127:0] data;

  function new(string name="order_item");
    super.new(name);
  endfunction

  virtual function string convert2string();
    return $sformatf("Data:0x%32x",data);
  endfunction

  virtual function void do_print(uvm_printer printer);
    if (printer.knobs.sprint == 0) begin
      $display(convert2string());
    end else begin
      printer.m_string = convert2string();
    end
  endfunction

  virtual function bit do_compare(uvm_object rhs, uvm_comparer comparer);
    order_item rhs_;
    if (!$cast(rhs_,rhs)) return 0;
    return (super.do_compare(rhs,comparer) && (data == rhs_.data));
  endfunction

  virtual function void do_copy(uvm_object rhs);
    order_item rhs_;
    if (!$cast(rhs_,rhs)) begin
      `uvm_fatal("ITEM","Cast failed in do_copy()")
    end
    super.do_copy(rhs);
    data = rhs_.data;
  endfunction

  virtual function void data_pack(ref bit [7:0] ret []);
    bit [127:0] cp = data;
    ret = new[16];
    foreach (ret[i]) begin
      ret[i] = cp[127:120];
      cp = cp << 8;
    end
  endfunction

  virtual function void unpack_data(bit [7:0] ret []);
    foreach (ret[i]) begin
      data[7:0] = ret[i];
      data = data << 8;
    end
  endfunction

endclass
