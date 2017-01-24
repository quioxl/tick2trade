class avalon_driver_base extends uvm_driver #(avalon_seq_item_base);

  `uvm_component_utils(avalon_driver_base)

  avalon_config cfg_h;
  virtual avalon_if vif;

  function new(string name, uvm_component parent);
    super.new(name,parent);
  endfunction

  function void build_phase(uvm_phase phase);
    if (cfg_h == null) begin
      cfg_h = avalon_config::get_config(this);
    end
    if (cfg_h == null)
      `uvm_fatal("DRV","Failed to pull cfg_h from config_db")
  endfunction

  function void connect_phase(uvm_phase phase);
    vif = cfg_h.vif;
  endfunction    

endclass