// Random sequence - generates 100 random transactions and sends them
// out on the chosen sequencer
class avalon_random_seq extends avalon_seq_base;

    `uvm_object_utils(avalon_random_seq)

    function new(string name = "avalon_random_seq");
      super.new(name);
    endfunction

    task body();
      trans_h = avalon_seq_item_base::type_id::create("trans_h");
      for (int i=0;i<100;i++) begin
        start_item(trans_h);
        if (!trans_h.randomize()) begin
          `uvm_fatal("SEQ","Transaction randomization failed")
        end
        `uvm_info("SEQ",$sformatf("Sending payload #%0d: %s",i,trans_h.convert2string),UVM_MEDIUM)
        finish_item(trans_h);
      end
    endtask

  endclass