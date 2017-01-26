// Avalon message item transaction
// Extends from sequence item base, simply constrains the size of messages to between 8 and 32 bytes
// as per assignment. 

class avalon_message_item extends avalon_seq_item_base;
  `uvm_object_utils(avalon_message_item)
  
  function new(string name = "avalon_message_item");
    super.new(name);
  endfunction

  constraint msg_size_c { payload.size >= 8; payload.size <= 32; }

  // Now that the payload size is more reasonable, include it in the convert2string output
  virtual function string convert2string();
    return $sformatf("Size:%0d [%u]",payload.size(),payload);
  endfunction
  
endclass