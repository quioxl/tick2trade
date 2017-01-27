class feed_scoreboard extends uvm_component;
  `uvm_component_utils(feed_scoreboard)

  uvm_analysis_imp_FEED_ACTUAL #(avalon_seq_item_base,feed_scoreboard) actual_ai;
  uvm_analysis_imp_FEED_EXPECT #(avalon_message_item,feed_scoreboard) expect_ai;

  avalon_message_item expect_q [$], actual_q [$];

  feed_env_config cfg_h;

  int compare_count,miscompare_count;

  function new(string name, uvm_component parent);
    super.new(name,parent);
  endfunction

  function void build_phase(uvm_phase phase);
    actual_ai = new("actual_ai",this);
    expect_ai = new("expect_ai",this);
  endfunction

  function void write_FEED_ACTUAL(avalon_seq_item_base t);
    avalon_message_item copy_h;
    if (cfg_h.enable_sb == 1'b0) begin
      return;
    end
    // The type of object coming in is the base item, so we have to copy
    // contents into the message_item class manually (even though there is
    // a class relationship it isn't possible to upcast in this situation)
    copy_h = avalon_message_item::type_id::create("copy_h");
    copy_h.payload = t.payload;
    // This isn't really needed but future enhancements to avalon_message_item may require it
    copy_h.msg_unpack();
    `uvm_info("SB",$sformatf("Received feed ACTUAL transaction: %s",copy_h.convert2string()),UVM_MEDIUM)
    if (expect_q.size() > actual_q.size()) begin
      compare_items(expect_q.pop_front(),copy_h);
    end else begin
      // No need to make a new copy, we did that already
      actual_q.push_back(copy_h);
    end
  endfunction

  function void write_FEED_EXPECT(avalon_message_item t);
    avalon_message_item clone_h;
    if (cfg_h.enable_sb == 1'b0) begin
      return;
    end
    `uvm_info("SB",$sformatf("Received feed EXPECT transaction: %s",t.convert2string()),UVM_MEDIUM)
    if (actual_q.size() > expect_q.size()) begin
      compare_items(t,actual_q.pop_front());
    end else begin
      if (!$cast(clone_h,t.clone())) begin
        `uvm_fatal("SB","Clone of expect item failed")
      end
      expect_q.push_back(clone_h);
    end
  endfunction

  function void compare_items(avalon_message_item expect_h, avalon_message_item actual_h);
    if (!expect_h.compare(actual_h)) begin
      `uvm_error("SB",$sformatf("Miscompare!\n  Actual:%s\n  Expect:%s",actual_h.convert2string(),expect_h.convert2string()))
      miscompare_count++;
    end else begin
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

