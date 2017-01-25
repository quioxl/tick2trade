module symbol_test();
`include "uvm_macros.svh"

  import uvm_pkg::*;
  import symbol_map_pkg::*;
  
  symbol_mapper mapper = new();
  symbol_t symbol;
  map_mem_t map;

  int temp;
  

  initial begin
    //Fill up the queue with some symbols
    for (int ii = 0; ii < 1000; ii++) begin
      std::randomize(symbol);
      map = mapper.enable_symbol(symbol);
      `uvm_info("Symbol Test", $sformatf("Symbol: 16'h%04x is mapped to 14'h%04x with valid: %0x", symbol, map.addr, map.valid), UVM_LOW)
    end

    //Try to enable a symbol that already exists
    for (int ii = 0; ii < 10; ii++) begin
      symbol = mapper.find_random_symbol();
      map = mapper.enable_symbol(symbol);
      `uvm_info("Symbol Test", $sformatf("Symbol: 16'h%04x is mapped to 14'h%04x with valid: %0x", symbol, map.addr, map.valid), UVM_LOW)
    end

    //Remove some symbols and then add new ones
    for (int ii = 0; ii < 100; ii++) begin
      symbol = mapper.find_random_symbol();
      mapper.disable_symbol(symbol);
      std::randomize(symbol);
      map = mapper.enable_symbol(symbol);
      `uvm_info("Symbol Test", $sformatf("Symbol: 16'h%04x is mapped to 14'h%04x with valid: %0x", symbol, map.addr, map.valid), UVM_LOW)
    end
    for (int ii = 0; ii < 100; ii++) begin
      symbol = mapper.find_random_symbol();
      mapper.disable_symbol(symbol);
    end
    for (int ii = 0; ii < 100; ii++) begin
      std::randomize(symbol);
      map = mapper.enable_symbol(symbol);
      `uvm_info("Symbol Test", $sformatf("Symbol: 16'h%04x is mapped to 14'h%04x with valid: %0x", symbol, map.addr, map.valid), UVM_LOW)
    end

    
    
  end

  
  

endmodule : symbol_test
