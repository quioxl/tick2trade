class strategy_predictor extends uvm_subscriber #(avalon_seq_item_base);
  `uvm_component_utils(strategy_predictor)

  const string report_id = "STRATEGY_PREDICTOR";

  int          discarded[string];

  function new(string name, uvm_component parent);
    super.new(name,parent);
  endfunction

  //strategy_message_item strategy_trans_h;
  uvm_analysis_imp_host #(host_item, strategy_predictor) host_export;
  uvm_analysis_port #(order_item) ap;

  //Structures for holding information programed into the host interface ram
  host_order_t temp_order;
  host_order_t orders[symbol_t];

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    host_export = new("host_export",this);
    ap = new("ap",this);
    //Initialize discarded values to 0.  Not strickly required, but
    // removes warnings
    discarded["size"] = 0;
    discarded["price_volume"] = 0;
    discarded["no_symbol"] = 0;
    discarded["bad_type"] = 0;
  endfunction : build_phase
  
  function void write_host(host_item t);
    map_mem_t    sym_map;
    bit [1:0]    upper_symbol;
    host_trans_t temp = t.data;  //Get the data into a struct for easier access
    if (temp.cmd == RESET)
      orders.delete();
    else if (temp.cmd == LOAD) begin
      //Build the temp transfer until the valid comes in.  Then add that to the
      // the orders for comparison when a symbol message comes in.
      case (temp.ram)
        SYMBOL: begin
          //Check for valid or not
          // Figure out the two upper bits of the symbol by looking at byte_en
          case (temp.byte_en)
            24'h00_0003 : upper_symbol = 2'b00;
            24'h00_000c : upper_symbol = 2'b01;
            24'h00_0030 : upper_symbol = 2'b10;
            24'h00_00c0 : upper_symbol = 2'b11;
            default : `uvm_error(report_id, "Invalid byte_en for SYMBOL LOAD")
          endcase
          sym_map = temp.data >> (16 * upper_symbol);
          temp_order.symbol   = {upper_symbol, temp.addr[13:0]};
          temp_order.valid    = sym_map.valid;
          temp_order.map_addr = sym_map.addr;
          if (temp_order.valid == 0) begin
            //Invalid: delete from array to prevent inadvertant match
          //`uvm_info("STRAT_PRED", $sformatf("Symbol From Order: 16'h%04x", temp_order.symbol) , UVM_MEDIUM)
            orders.delete(temp_order.symbol);
          end else
            //Valid: add to array for matching purposes
            orders[temp_order.symbol] = temp_order;
        end // case: SYMBOL
        PRICE: begin
          temp_order.min_price = temp.data[63:0];
          temp_order.max_price = temp.data[127:64];
        end
        VOLUME: begin
          temp_order.min_vol = temp.data[31:0];
          temp_order.max_vol = temp.data[63:32];
        end
        ORDER: begin
          temp_order.order = temp.data[127:0];
        end
        default: `uvm_error(report_id, "Unknown ram specified")
      endcase
    end else
      `uvm_error("strategy_predictor", "Unknown command type received")
  endfunction : write_host

  function void write(avalon_seq_item_base t);
    host_order_t order;
    order_item   out_order;
    feed_message_item feed_item;

    if (t.payload.size() != 17) begin
      //Currently, we only care about "NEW" messages of size 17 bytes
      discarded["size"]++;
    end else begin
      //If we do have a message 17 bytes long, then lets see if it is nice message of "NEW"
      feed_item = feed_message_item::type_id::create("feed_item");
      feed_item.payload = t.payload;
      feed_item.msg_unpack();
      if (feed_item.msg_type == "NEW") begin //Match the "New" message type
        if (orders.exists(feed_item.symbol_id)) begin //Check if the symbol has been programmed
          //`uvm_info("STRAT_PRED", $sformatf("Symbol From Feed: 16'h%04x", feed_item.symbol_id) , UVM_MEDIUM)
          order = orders[feed_item.symbol_id];
          if (feed_item.volume > order.min_vol &&
              feed_item.volume < order.max_vol &&
              feed_item.price > order.min_price &&
              feed_item.price < order.max_price) begin
            out_order = order_item::type_id::create("out_order");
            out_order.data = order.order;
            ap.write(out_order);
          end else begin
            discarded["price_volume"]++;
          end
        end else begin // if (orders.exists(feed_item.symbol_id))
          discarded["no_symbol"]++;
        end // else: !if(orders.exists(feed_item.symbol_id))
      end else begin // if (feed_item.msg_type == "NEW")
        discarded["bad_type"]++;
      end // else: !if(feed_item.msg_type == "NEW")
    end // else: !if(t.payload.size() != 17)
  endfunction

  function void report_phase(uvm_phase phase);
    `uvm_info(report_id, $sformatf("Total Discarded Messages: %0d", discarded.sum()), UVM_LOW)
    `uvm_info(report_id, $sformatf("%p", discarded), UVM_LOW)
  endfunction

endclass