class random_host_program_seq extends uvm_sequence #(host_item);

  `uvm_object_utils(random_host_program_seq)

  int trans_count = 5;
  

  function new(string name = "random_host_program_seq");
    super.new(name);
  endfunction

  task body();
    host_symbol_seq symbol_seq_h;
    symbol_seq_h = host_symbol_seq::type_id::create("symbol_seq_h");
    repeat (trans_count) begin
      if (!symbol_seq_h.randomize()) begin
        `uvm_fatal("SEQ","Sequence randomization failed")
      end
      //`uvm_info("SEQ",$sformatf("Sending feed message: %s",feed_trans_h.convert2string()),UVM_MEDIUM)
      symbol_seq_h.start(m_sequencer);
    end
  endtask

endclass : random_host_program_seq