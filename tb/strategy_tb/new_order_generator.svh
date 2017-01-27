class new_order_generator extends uvm_subscriber #(order_item);

  `uvm_component_utils(new_order_generator)

  //Data members
  host_symbol_seq symbol_seq_h;
  uvm_sequencer #(host_item) host_seqr_h;

  //Methods
  function new(string name, uvm_component parent);
    super.new(name,parent);
    symbol_seq_h = host_symbol_seq::type_id::create("symbol_seq_h");
  endfunction : new

  function void end_of_elaboration_phase(uvm_phase phase);
    super.end_of_elaboration_phase(phase);
    if (host_seqr_h == null)
      `uvm_fatal("new_order_generator", "order_seqr not set by the environment")
  endfunction : end_of_elaboration_phase
  
  function void write(order_item t);
    //Find the symbol
    symbol_t symbol = t.data[127:112];
    //Create new symbol entry
    symbol_seq_h.sym_update = 1;
    if (!symbol_seq_h.randomize() with
          {symbol == local::symbol; }) begin
      `uvm_fatal("SEQ","Sequence randomization failed")
    end
    fork //Must fork/join_none becuase write() is a function
      symbol_seq_h.start(host_seqr_h);
    join_none
  endfunction : write

endclass : new_order_generator