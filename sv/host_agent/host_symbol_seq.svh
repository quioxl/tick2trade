class host_symbol_seq extends uvm_sequence #(host_item);

  `uvm_object_utils(host_symbol_seq)

  //Data Members
  rand symbol_t      symbol;
  rand bit [31:0]    min_vol;
  rand bit [31:0]    max_vol;
  rand bit [63:0]    min_price;
  rand bit [63:0]    max_price;
  rand bit [127:0]   order;
  bit                sym_update;
  
  map_mem_t     map_addr;
  symbol_mapper mapper = symbol_mapper::get_mapper();

  //Constraints
  constraint volume_c { soft min_vol < max_vol; }
  constraint price_c  { soft min_price < max_price; }

  //Methods
  function new(string name = "host_symbol_seq");
    super.new(name);
  endfunction : new

  task body();
    host_trans_t temp;
    //Make sure the reserved and unused fields are cleared to 0
    temp.res = 'h0;
    temp.unused = 'h0;
    
    req = host_item::type_id::create("req");
    //Get the symbol address mapping
    map_addr = mapper.enable_symbol(symbol);
    if (sym_update == 1) begin
      start_item(req);
      //Have to invalidate the memory first
      map_addr.valid = 0;
      temp.cmd     = LOAD;
      temp.ram     = SYMBOL;
      temp.addr    = symbol[13:0];
      temp.byte_en = 2'b11 << (2 * symbol[15:14]);
      temp.data    = map_addr << (16 * symbol[15:14]);
      req.data = temp;
      finish_item(req);
    end // if (sym_update == 1)

    //Update the prices
    start_item(req);
    temp.cmd     = LOAD;
    temp.ram     = PRICE;
    temp.addr    = map_addr.addr;
    temp.byte_en = 24'h00_ffff;
    temp.data    = {max_price, min_price};
    req.data = temp;
    finish_item(req);

    //Update the volumes
    start_item(req);
    temp.cmd     = LOAD;
    temp.ram     = VOLUME;
    temp.addr    = map_addr.addr;
    temp.byte_en = 24'h00_00ff;
    temp.data    = {max_vol, min_vol};
    req.data = temp;
    finish_item(req);

    //Update the order
    start_item(req);
    temp.cmd     = LOAD;
    temp.ram     = ORDER;
    temp.addr    = map_addr.addr;
    temp.byte_en = 24'h00_ffff;
    temp.data    = order;
    req.data = temp;
    finish_item(req);

    //Validate the symbol in memory
    start_item(req);
    map_addr.valid = 1;
    temp.cmd     = LOAD;
    temp.ram     = SYMBOL;
    temp.addr    = symbol[13:0];
    temp.byte_en = 2'b11 << (2 * symbol[15:14]);
    temp.data    = map_addr << (16 * symbol[15:14]);
    req.data = temp;
    finish_item(req);
  endtask : body

  task change_symbol_info(symbol_t      sym,
                          bit [31:0]    min_volume,
                          bit [31:0]    max_volume,
                          bit [63:0]    min_pric,
                          bit [63:0]    max_pric,
                          bit [127:0]   the_order,
                          uvm_sequencer #(host_item) seqr,
                          bit           update = 0);
    //Store the values
    symbol     = sym;
    min_vol    = min_volume;
    max_vol    = max_volume;
    min_price  = min_pric;
    max_price  = max_pric;
    order      = the_order;
    sym_update = update;
    //Start the sequence
    this.start(seqr);
  endtask : change_symbol_info
    
  

endclass : host_symbol_seq
