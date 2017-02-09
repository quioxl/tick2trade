class strategy_scoreboard extends uvm_component;
  `uvm_component_utils(strategy_scoreboard)

  uvm_analysis_imp_STRATEGY_ACTUAL #(order_item,strategy_scoreboard) actual_ai;
  uvm_analysis_imp_STRATEGY_EXPECT #(order_item,strategy_scoreboard) expect_ai;

  order_item expect_q [$], actual_q [$];

  bit enable_sb = 1;
  //strategy_env_config cfg_h;

  int compare_count,miscompare_count;

  function new(string name, uvm_component parent);
    super.new(name,parent);
  endfunction

  function void build_phase(uvm_phase phase);
    actual_ai = new("actual_ai",this);
    expect_ai = new("expect_ai",this);
  endfunction

  function void write_STRATEGY_ACTUAL(order_item t);
    if (enable_sb == 1'b0) begin
      return;
    end
    `uvm_info("SB",$sformatf("Received strategy ACTUAL transaction: %s",t.convert2string()),UVM_LOW)
    if (expect_q.size() > actual_q.size()) begin
      compare_items(expect_q.pop_front(),t);
    end else begin
      actual_q.push_back(t);
    end
  endfunction

  function void write_STRATEGY_EXPECT(order_item t);
    order_item copy_item;
    uvm_object clone_item;
    if (enable_sb == 1'b0) begin
      return;
    end
    clone_item = t.clone();
    if (!$cast(copy_item,clone_item)) begin
      `uvm_fatal("SB","Clone failed")
    end
    `uvm_info("SB",$sformatf("Received strategy EXPECT transaction: %s",copy_item.convert2string()),UVM_LOW)
    if (actual_q.size() > expect_q.size()) begin
      compare_items(copy_item,actual_q.pop_front());
    end else begin
      expect_q.push_back(copy_item);
    end
  endfunction

  function void compare_items(order_item expect_h, order_item actual_h);
    if (!expect_h.compare(actual_h)) begin
      `uvm_error("SB",$sformatf("Miscompare!\nActual:%s\nExpect:%s",actual_h.convert2string(),expect_h.convert2string()))
      miscompare_count++;
    end else begin
      `uvm_info("SB",$sformatf("Match: %s",actual_h.convert2string()),UVM_MEDIUM)
      compare_count++;
    end
  endfunction

  function void report_phase(uvm_phase phase);
    `uvm_info("SB",$sformatf("Transactions compared:%0d Miscompares:%0d",miscompare_count+compare_count,miscompare_count),UVM_LOW)
  endfunction

  function void phase_ready_to_end(uvm_phase phase);
    if (((expect_q.size()!=0) | (actual_q.size()!=0)) & phase.is(uvm_post_shutdown_phase::get())) begin
      fork
        wait_for_done(phase);
      join_none
    end
  endfunction

  task wait_for_done(uvm_phase phase);
    phase.raise_objection(this);
    fork
      begin : WAIT_BLOCK
        while ((expect_q.size()!=0) | (actual_q.size()!=0)) #1us;
        disable TIMEOUT_BLOCK;
      end
      begin : TIMEOUT_BLOCK
        #10us;
        `uvm_error("SB","Timed out waiting for scoreboard queues to empty")
        expect_q = {};
        actual_q = {};
        disable WAIT_BLOCK;
      end
    join
    phase.drop_objection(this);
  endtask

endclass

