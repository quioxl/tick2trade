class new_order_generator extends uvm_subscriber #(order_item);

  `uvm_component_utils(new_order_generator)

  //Data members
  symbol_t outstanding_symbols[$];
  event new_symbol;
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
    outstanding_symbols.push_back(t.data[127:112]);
    -> new_symbol;
  endfunction : write

  task run_phase(uvm_phase phase);
    symbol_t symbol;
    forever begin
      @(new_symbol);
      do begin
        //Create new symbol entry
        symbol = outstanding_symbols.pop_front();
        symbol_seq_h.sym_update = 1;
        if (!symbol_seq_h.randomize() with
            {symbol == local::symbol; }) begin
          `uvm_fatal("SEQ","Sequence randomization failed")
        end
        symbol_seq_h.start(host_seqr_h);
      end while (outstanding_symbols.size() != 0);
    end // forever begin
  endtask : run_phase
  
endclass : new_order_generator