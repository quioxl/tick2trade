class avalon_monitor extends uvm_monitor;

  `uvm_component_utils(avalon_monitor)

  uvm_analysis_port #(avalon_message_seq_item_base) ap;

  virtual avalon_if vif;

  avalon_message_seq_item_base trans_h;

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
    vif.in_ready <= 1'b1;
    trans_h = avalon_message_seq_item_base::type_id::create("trans_h");
    forever begin
      @(posedge vif.clk);
      while (vif.in_valid == 1'b0) @(posedge vif.clk);
      while (vif.in_endofpacket == 1'b0) begin
        p.push_back(vif.in_data);
        @(posedge vif.clk);
        while (vif.in_valid == 1'b0) @(posedge vif.clk);
      end
      p.push_back(vif.in_data);
      empty = vif.in_empty;
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
      repeat (empty) void'(b.pop_back());
      trans_h.payload = b;
      ap.write(trans_h);
    end
  endtask

endclass
