class feed_scoreboard extends uvm_component;
  `uvm_component_utils(feed_scoreboard)

  uvm_analysis_imp_FEED_ACTUAL #(avalon_seq_item_base,feed_scoreboard) actual_ai;
  uvm_analysis_imp_FEED_EXPECT #(feed_message_item,feed_scoreboard) expect_ai;

  feed_message_item expect_q [$], actual_q [$];

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
    feed_message_item cast_item;
    if (cfg_h.enable_sb == 1'b0) begin
      return;
    end
    cast_item = feed_message_item::type_id::create("cast_item");
    cast_item.payload = t.payload;
    cast_item.msg_unpack();
    `uvm_info("SB",$sformatf("Received feed ACTUAL transaction: %s",cast_item.convert2string()),UVM_LOW)
    if (expect_q.size() > actual_q.size()) begin
      compare_items(expect_q.pop_front(),cast_item);
    end else begin
      actual_q.push_back(cast_item);
    end
  endfunction

  function void write_FEED_EXPECT(feed_message_item t);
    feed_message_item copy_item;
    uvm_object clone_item;
    if (cfg_h.enable_sb == 1'b0) begin
      return;
    end
    clone_item = t.clone();
    if (!$cast(copy_item,clone_item)) begin
      `uvm_fatal("SB","Clone failed")
    end
    `uvm_info("SB",$sformatf("Received feed EXPECT transaction: %s",copy_item.convert2string()),UVM_LOW)
    if (actual_q.size() > expect_q.size()) begin
      compare_items(copy_item,actual_q.pop_front());
    end else begin
      expect_q.push_back(copy_item);
    end
  endfunction

  function void compare_items(feed_message_item expect_h, feed_message_item actual_h);
    if (!expect_h.compare(actual_h)) begin
      `uvm_error("SB",$sformatf("Miscompare!\nActual:%s\nExpect:%s",actual_h.convert2string(),expect_h.convert2string()))
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

