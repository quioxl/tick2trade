class incr_host_program_seq extends uvm_sequence #(host_item);

  `uvm_object_utils(incr_host_program_seq)

  int trans_count = 5;
  

  function new(string name = "incr_host_program_seq");
    super.new(name);
  endfunction

  task body();
    host_symbol_seq symbol_seq_h;
    symbol_seq_h = host_symbol_seq::type_id::create("symbol_seq_h");
    for (int ii = 0; ii < trans_count; ii++) begin
      symbol_seq_h.change_symbol_info(ii, 'h0, 'hffff_ffff, 'h0, 'hffff_ffff_ffff_ffff, {ii, 112'hdeadbeef}, m_sequencer);
    end
  endtask

endclass : incr_host_program_seq
