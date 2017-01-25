class strategy_predictor extends uvm_subscriber #(avalon_seq_item_base);
  `uvm_component_utils(strategy_predictor)

  function new(string name, uvm_component parent);
    super.new(name,parent);
  endfunction

  //strategy_message_item strategy_trans_h;
  uvm_analysis_imp_host #(host_item, strategy_predictor) host_export;
  uvm_analysis_port #(avalon_seq_item_base) ap;  //CHECK_ME: Needs to be updated to order type

  //Structures for holding information programed into the host interface ram
  host_order_t temp_order;
  host_order_t orders[symbol_t];

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    host_export = new("host_export",this);
    ap = new("ap",this);
  endfunction : build_phase
  
  function void write_host(host_item t);
    //Build the temp transfer until the valid comes in.  Then add that to the
    // the orders for comparison when a symbol message comes in.  
  endfunction : write_host

  function void write(avalon_seq_item_base t);
    //Use the values stored in the mapper to see if a match exists.
    // If it does, then send the order information to the scoreboard.
    
/* -----\/----- EXCLUDED -----\/-----
    if (t.payload.size() != 17) begin
      return;
    end
    strategy_trans_h = strategy_message_item::type_id::create("strategy_trans_h");
    strategy_trans_h.payload = t.payload;
    strategy_trans_h.msg_unpack();
    if (strategy_trans_h.msg_type != "NEW") begin
      return;
    end
    ap.write(strategy_trans_h);
 -----/\----- EXCLUDED -----/\----- */
  endfunction

endclass