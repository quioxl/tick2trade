// Base sequence for Avalon - defines a transaction handle for use in child sequences
class avalon_seq_base extends uvm_sequence #(avalon_seq_item_base,avalon_seq_item_base);

    `uvm_object_utils(avalon_seq_base)

    avalon_seq_item_base trans_h;

    function new(string name = "avalon_seq_base");
      super.new(name);
    endfunction

    task body();
      `uvm_fatal("SEQ","No overridden body task")
    endtask

  endclass