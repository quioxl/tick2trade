// Avalon master driver class
//  Instantiated in the agent if configured as an ACTIVE MASTER.
//  Transactional data is pulled from a connected sequencer and 
//  sent out on the Avalon bus.

class avalon_master_driver extends avalon_driver_base;
  `uvm_component_utils(avalon_master_driver)

  function new(string name, uvm_component parent);
    super.new(name,parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
  endfunction

  virtual task run_phase(uvm_phase phase);
    REQ trans_h;
    bit [63:0] pdata [$];
    int bnum;
    int psize;
    bit [2:0] empty;
    // Initialize the output signals to inactive state
    vif.data <= 'b0;
    vif.valid <= 'b0;
    vif.startofpacket <= 0;
    vif.endofpacket <= 0;
    vif.empty <= 0;
    vif.error <= 0;
    forever begin
      seq_item_port.get_next_item(trans_h);
      // Initialize the payload queue (64-bits wide)
      pdata = {};
      bnum = 8;
      psize = 0;
      // Populate the payload queue from the byte-wide transaction data array
      foreach (trans_h.payload[i]) begin
        // Track the byte number.  First byte is going in upper-most part of the 64-bit word and
        // 8th byte is going in lower-most part (bits [7:0])
        pdata[psize] |= trans_h.payload[i] << (bnum-1)*8;
        if (--bnum == 0) begin
          // We've reached the end of a 64-bit word. Re-initialize the byte number and add a new
          // word to the endo of the payload array
          bnum = 8;
          psize++;
          pdata.push_back(0);
        end
      end
      // Calculate the empty field - the byte number value reflects this
      if (bnum == 8) begin
        empty = 0;
        // We need to pull the last word off the array, it was set up but not used
        void'(pdata.pop_back());
      end else begin
        empty = bnum;
      end
      // Now drive the bus, but wait for ready to be high first
      wait_for_ready();
      foreach (pdata[i]) begin
        // For each beat, need to do the following (ready may not be high when we start, keep that in mind):
        // 1. Drive new values on the bus
        // 1. Check value of ready. If low, maintain bus with valid low until ready goes high, then drive previous values for
        //    one more cycle with valid high
        // 4. Move to next loop iteration
        vif.data <= pdata[i];
        if (i==0) begin
          vif.startofpacket <= 1'b1;
        end else begin
          vif.startofpacket <= 1'b0;
        end
        if (i==pdata.size()-1) begin
          vif.endofpacket <= 1'b1;
          vif.empty <= empty;
        end else begin
          vif.endofpacket <= 1'b0;
          vif.empty <= 'b0;
        end
        if (vif.ready !== 1'b1) begin
          wait_for_ready();
        end
        vif.valid <= 1'b1;
        @(posedge vif.clk);
      end
      vif.valid <= 1'b0;
      vif.endofpacket <= 1'b0;
      vif.empty <= 'b0;
      vif.data <= 'b0;
      vif.startofpacket <= 'b0;
      repeat (trans_h.delay_gap) begin
        vif.valid <= 1'b0;
        vif.endofpacket <= 1'b0;
        vif.empty <= 'b0;
        vif.data <= 'b0;
        @(posedge vif.clk);
      end
      seq_item_port.item_done();
    end
  endtask

  virtual task wait_for_ready();
    bit done = 0;
    int count = 0;
    fork
      begin : TIMEOUT_BLOCK
        repeat (cfg_h.timeout) begin
          @(posedge vif.clk);
        end
        `uvm_fatal("DRV","Timeout waiting for ready, exiting")
      end
      begin : WAIT_BLOCK
        do begin
          vif.valid <= 1'b0;
          @(posedge vif.clk);
        end while (vif.ready !== 1'b1);
        disable TIMEOUT_BLOCK;
      end
    join
  endtask

endclass



