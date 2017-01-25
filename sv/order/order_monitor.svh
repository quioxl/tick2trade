class order_monitor extends uvm_component;

  `uvm_component_utils(order_monitor)

  uvm_analysis_port #(order_item) ap;

  virtual order_interface vif;
  order_config cfg_h;

  function new(string name, uvm_component parent);
    super.new(name,parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    ap = new("ap",this);
  endfunction

  virtual function void connect_phase(uvm_phase phase);
    if (cfg_h == null) begin
      cfg_h = order_config::get_config(this);
    end
    if (cfg_h == null) begin
      `uvm_fatal("MON","Unable to fetch config object from db")
    end
    vif = cfg_h.vif;
  endfunction

  virtual task run_phase(uvm_phase phase);
    order_item trans_h = order_item::type_id::create("trans_h");
    cfg_h.wait_for_reset();
    forever begin
      @(posedge vif.valid);
      trans_h.data = vif.data;
      ap.write(trans_h);
    end
  endtask

endclass



