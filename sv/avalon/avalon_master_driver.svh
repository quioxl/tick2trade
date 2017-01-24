class avalon_master_driver extends avalon_driver_base;
  `uvm_component_utils(avalon_master_driver)

  // REQ full_payload [$];
  // int full_payload_size;

  // rand int next_accum_size;

  // constraint accum_c { next_accum_size >= 1; 
  //                      next_accum_size <= 1500; }

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
    // if (!this.randomize())
    //   `uvm_fatal("DRV","Self-randomization failed")
    vif.data <= 'b0;
    vif.valid <= 'b0;
    vif.startofpacket <= 0;
    vif.endofpacket <= 0;
    vif.empty <= 0;
    vif.error <= 0;
    forever begin
      seq_item_port.get_next_item(trans_h);
      // trans_h.msg_pack();
      // if (trans_h.payload.size() + full_payload_size >= next_accum_size) begin
      //   // The accumulated payload size has gotten big enough to send based on the random accumulated size.
      //   // Build it up and send the data, re-randomize accumulation size.
      //   build_and_send();
      // end
      // if (trans_h.payload.size() >= next_accum_size) begin
      //   // The re-randomized accumulation size is small and the current message exceeds it.. Send this one too
      //   full_payload.push_back(trans_h);
      //   full_payload_size += trans_h.payload.size();
      //   build_and_send();
      // end else if ((trans_h.message_count > 0) && (trans_h.message_count <= full_payload.size())) begin
      //   // The transaction has a non-zero message count and we're ready to send that many messages. Send what
      //   // we've accumulated.
      //   full_payload.push_back(trans_h);
      //   full_payload_size += trans_h.payload.size();
      //   build_and_send();
      // end
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
      // Now drive the bus
      foreach (pdata[i]) begin
        // If target is not ready, advance clock until ready is high and drive valid low
        if (vif.ready == 1'b0) begin
          do begin
            vif.valid <= 1'b0;
            @(posedge vif.clk);
          end while (vif.ready == 1'b0);
          // Once ready has gone high again, drive valid one additional cycle so the 
          // data that was put on the bus earlier can get picked up.
          vif.valid <= 1'b1;
          @(posedge vif.clk);
        end else begin
          @(posedge vif.clk);
        end
        // Drive valid high and put data on bus
        vif.valid <= 1'b1;
        vif.data <= pdata[i];
        // If first word of data, drive startofpacket
        if (i==0) begin
          vif.startofpacket <= 1'b1;
        end else begin
          vif.startofpacket <= 1'b0;
        end
        // If last word of data, drive endofpacket and empty field
        if (i==pdata.size()-1) begin
          vif.endofpacket <= 1'b1;
          vif.empty <= empty;
        end else begin
          vif.endofpacket <= 1'b0;
          vif.empty <= 'b0;
        end
      end
      // Insert delay gap
      repeat (trans_h.delay_gap) begin
        @(posedge vif.clk);
        vif.valid <= 1'b0;
        vif.endofpacket <= 1'b0;
        vif.empty <= 'b0;
        vif.data <= 'b0;
      end
      seq_item_port.item_done();
    end
  endtask

endclass



