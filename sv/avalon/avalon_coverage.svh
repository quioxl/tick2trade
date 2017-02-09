class avalon_coverage extends uvm_subscriber #(avalon_seq_item_base);
  `uvm_component_utils(avalon_coverage)

  avalon_seq_item_base trans_h;

  covergroup avalon_cov;
    cp_size: coverpoint trans_h.payload.size() {
      bins MIN = { 8 };
      bins MID = {[9:31]};
      bins MAX = { 32 };
    }
  endgroup

  function new(string name, uvm_component parent);
    super.new(name,parent);
    avalon_cov = new;
  endfunction

  function void write(avalon_seq_item_base t);
    `uvm_info("COV",$sformatf("Saw item: %s",t.convert2string()),UVM_MEDIUM)
    trans_h = t;
    avalon_cov.sample();
  endfunction

endclass