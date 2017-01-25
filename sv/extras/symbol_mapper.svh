class symbol_mapper extends uvm_object;

  `uvm_object_utils(symbol_mapper)

  //This is going to be a singleton class
  static symbol_mapper single_mapper;

  //16-bit symbols are mapped to 14-bit addresses with a 1-bit valid.
  // The valid and 14-bit address are stored in this format:
  //  16'h{valid, 1'b0, 14'b{map_addr}}
  map_mem_t  map_addrs [symbol_t];
  symbol_t active_symbols [$];

  map_addr_t addr_counter = 0;
  map_addr_t addr_recycle [$];
  
  function new(string name = "symbol_mapper");
    super.new(name);
  endfunction : new

  static function symbol_mapper get_mapper();
    if (single_mapper == null) 
      single_mapper = symbol_mapper::type_id::create("single_mapper");
    return single_mapper;
  endfunction : get_mapper;

  function map_addr_t get_next_map_addr();
    if (addr_recycle.size() != 0)
      return addr_recycle.pop_front();
    else
      //Possibly want to enable randomization of count
      return addr_counter++; //CHECK_THIS
  endfunction : get_next_map_addr


  function map_mem_t enable_symbol(symbol_t symbol);
    if (map_addrs.exists(symbol) && map_addrs[symbol].valid == 1) begin
      `uvm_info("Symbol Mapper", $sformatf("Symbol: 16'h%04x is already mapped", symbol), UVM_MEDIUM)
      return map_addrs[symbol];
    end else begin
      active_symbols.push_back(symbol);
      enable_symbol.valid = 1'b1;
      enable_symbol.addr = get_next_map_addr();
      map_addrs[symbol] = enable_symbol;
      return enable_symbol;
    end
  endfunction : enable_symbol

  function map_addr_t lookup_symbol(symbol_t symbol);
    return map_addrs[symbol];
  endfunction : lookup_symbol

  function void disable_symbol(symbol_t symbol);
    int index[$] = active_symbols.find_index with ( item == symbol);
    active_symbols.delete(index[0]);
    //map_addrs[symbol].valid = 0;
    addr_recycle.push_back(map_addrs[symbol].addr);
    map_addrs.delete(symbol);
  endfunction : disable_symbol

  function symbol_t find_random_symbol();
    int temp = $urandom_range(0, active_symbols.size()-1);
    return active_symbols[temp];
  endfunction : find_random_symbol
    
  
endclass : symbol_mapper