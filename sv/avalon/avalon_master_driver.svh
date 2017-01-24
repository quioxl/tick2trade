class avalon_master_driver extends uvm_driver#(avalon_message_seq_item_base);
  `uvm_component_utils(avalon_master_driver)

  REQ full_payload [$];
  int full_payload_size;

  rand int next_accum_size;

  avalon_config cfg_h;

  virtual avalon_if vif;

  constraint accum_c { next_accum_size >= 1; 
                       next_accum_size <= 1500; }

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

  task run_phase(uvm_phase phase);
    REQ trans_h;
    if (!this.randomize())
      `uvm_fatal("DRV","Self-randomization failed")
    forever begin
      seq_item_port.get_next_item(trans_h);
      trans_h.pack_msg();
      if (trans_h.payload.size() + full_payload_size >= next_accum_size) begin
        // The accumulated payload size has gotten big enough to send based on the random accumulated size.
        // Build it up and send the data, re-randomize accumulation size.
        build_and_send();
      end
      if (trans_h.payload.size() >= next_accum_size) begin
        // The re-randomized accumulation size is small and the current message exceeds it.. Send this one too
        full_payload.push_back(trans_h);
        full_payload_size += trans_h.payload.size();
        build_and_send();
      end else if ((trans_h.message_count > 0) && (trans_h.message_count <= full_payload.size())) begin
        // The transaction has a non-zero message count and we're ready to send that many messages. Send what
        // we've accumulated.
        full_payload.push_back(trans_h);
        full_payload_size += trans_h.payload.size();
        build_and_send();
      end
      seq_item_port.item_done();
    end
  endtask

  task build_and_send();
    bit [63:0] pdata [$];
    int bnum;
    int psize = 0;
    bit [2:0] empty;
    pdata.push_back(0);
    pdata[psize][63:48] = full_payload.size();
    bnum = 6;
    foreach (full_payload[i]) begin
      foreach (full_payload[i].payload[j]) begin
        if (bnum==8) begin
          pdata.push_back(0);
          psize++;
        end
        pdata[psize] |= full_payload[i].payload[j] << (bnum-1)*8; 
        if (--bnum == 0) begin
          bnum = 8;
        end
      end
    end
    if (bnum == 8) begin
      empty = 0;
    end else begin
      empty = bnum;
    end
    foreach (pdata[i]) begin
      @(posedge vif.clk);
      while (vif.ready == 1'b0) begin
        vif.in_valid <= 1'b0;
        @(posedge vif.clk);
      end
      vif.in_valid <= 1'b1;
      vif.in_data <= pdata[i];
      if (i==0) begin
        vif.in_startofpacket <= 1'b1;
      end else begin
        vif.in_startofpacket <= 1'b0;
      end
      if (i==pdata.size()-1) begin
        vif.in_endofpacket <= 1'b1;
        vif.in_empty <= empty;
      end else begin
        vif.in_endofpacket <= 1'b0;
        vif.in_empty <= 'b0;
      end
    end
    full_payload = {};
    full_payload_size = 0;
    if (!this.randomize())
      `uvm_fatal("DRV","Self-randomization failed")
  endtask

endclass



