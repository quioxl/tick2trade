class avalon_seq_base extends uvm_sequence #(avalon_message_seq_item_base,avalon_message_seq_item_base);

    `uvm_object_utils(avalon_seq_base)

    function new(string name = "avalon_seq_base");
      super.new(name);
    endfunction

    task body();
      `uvm_fatal("SEQ","No overridden body task")
    endtask

  endclass