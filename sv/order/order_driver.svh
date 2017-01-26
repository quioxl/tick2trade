class order_driver extends uvm_driver #(order_item);
  `uvm_component_utils(order_driver)

  virtual order_interface vif;
  order_config cfg_h;

  function new(string name, uvm_component parent);
    super.new(name,parent);
  endfunction

  virtual function void connect_phase(uvm_phase phase);
    if (cfg_h == null) begin
      cfg_h = order_config::get_config(this);
    end
    if (cfg_h == null) begin
      `uvm_fatal("DRV","Config object uninitialized")
    end
    vif = cfg_h.vif;
  endfunction

  virtual task run_phase(uvm_phase phase);
    vif.ready <= 1'b0;
    cfg_h.wait_for_reset();
    vif.ready <= 1'b1;
    forever begin
      @(posedge vif.valid);
      @(posedge vif.clk);
      randcase
        cfg_h.stall_frequency : begin
          vif.ready <= 1'b0;
          repeat ($urandom_range(cfg_h.min_stall_width,cfg_h.max_stall_width)) @(posedge vif.clk);
          vif.ready <= 1'b1;
        end
        (100-cfg_h.stall_frequency) : vif.ready <= 1'b1;
      endcase
    end
  endtask

endclass