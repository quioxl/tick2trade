// Avalon agent monitor
// Snoops Avalon bus and generates transactions based on activity seen

class avalon_monitor extends uvm_monitor;

  `uvm_component_utils(avalon_monitor)

  uvm_analysis_port #(avalon_seq_item_base) ap;

  virtual avalon_if vif;

  avalon_seq_item_base trans_h;

  avalon_config cfg_h;

  function new(string name, uvm_component parent);
    super.new(name,parent);
  endfunction

  function void build_phase(uvm_phase phase);
    if (cfg_h == null) begin
      cfg_h = avalon_config::get_config(this);
    end
    if (cfg_h == null)
      `uvm_fatal("MON","Failed to pull cfg_h from config_db")
    ap = new("ap",this);
  endfunction

  function void connect_phase(uvm_phase phase);
    vif = cfg_h.vif;
  endfunction

  task run_phase(uvm_phase phase);
    bit [63:0] p [$];
    bit [7:0] b [$];
    bit [2:0] empty;
    trans_h = avalon_seq_item_base::type_id::create("trans_h");
    // Don't start looking for activity until reset is deasserted
    cfg_h.wait_for_reset();
    forever begin
      @(posedge vif.clk);
      // Wait for valid to go high
      while (vif.valid !== 1'b1) @(posedge vif.clk);
      // We don't do protocol checking here, that is for assertions. All we care about
      // at this point is the endofpacket signal going high.  While it isn't,
      // push a beat-worth of data into the accumulator
      while (vif.endofpacket !== 1'b1) begin
        p.push_back(vif.data);
        `uvm_info("MON",$sformatf("Pushed 0x%16x onto queue",vif.data),UVM_HIGH)
        @(posedge vif.clk);
        // If valid went low again, move clock forward until it is high
        while (vif.valid !== 1'b1) @(posedge vif.clk);
      end
      // Last push (this is what came in during endofpacket==1)
      p.push_back(vif.data);
      empty = vif.empty;
      // Unpack beat data into the byte queue
      foreach (p[i]) begin
        b.push_back(p[i][63:56]);
        b.push_back(p[i][55:48]);
        b.push_back(p[i][47:40]);
        b.push_back(p[i][39:32]);
        b.push_back(p[i][31:24]);
        b.push_back(p[i][23:16]);
        b.push_back(p[i][15:8]);
        b.push_back(p[i][7:0]);
      end
      // Pop off the back enough times to drop the empty bytes
      repeat (empty) void'(b.pop_back());
      // Set up the transaction
      trans_h.payload = b;
      b = {};
      p = {};
      // Push transaction out to the analysis port
      ap.write(trans_h);
    end
  endtask

endclass
