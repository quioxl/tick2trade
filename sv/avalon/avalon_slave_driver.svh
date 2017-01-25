class avalon_slave_driver extends avalon_driver_base;

  `uvm_component_utils(avalon_slave_driver)

  function new(string name, uvm_component parent);
    super.new(name,parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
  endfunction

  virtual task run_phase(uvm_phase phase);
    bit in_packet = 0;
    // This is an odd slave driver because the data is unidirectional
    // going in, i.e. there is no need to provide any stimulus out aside
    // from a READY signal to halt data from time to time. Instead of embedding
    // this in a sequence item, configuration info is used to determine the
    // frequency and duration of stalls out of this driver.
    vif.ready <= 1'b1;
    vif.error <= 1'b0;
    forever begin
      @(posedge vif.clk);
      if (vif.startofpacket == 1'b1) begin
        in_packet = 1;
      end
      if (vif.endofpacket == 1'b1) begin
        in_packet = 0;
      end
      if (in_packet == 1'b1 && vif.valid == 1'b1) begin
        randcase 
          cfg_h.slave_stall_frequency : begin
            vif.ready <= 1'b0;
            repeat ($urandom_range(cfg_h.slave_min_stall,cfg_h.slave_max_stall)) @(posedge vif.clk);
            vif.ready <= 1'b1;
          end
          (100-cfg_h.slave_stall_frequency) : vif.ready <= 1'b1;
        endcase
      end
    end
  endtask

endclass  