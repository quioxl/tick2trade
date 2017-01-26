package symbol_map_pkg;
`include "uvm_macros.svh"

  import uvm_pkg::*;

  //Typedefs
  typedef bit[15:0]  symbol_t;
  typedef bit[13:0]  map_addr_t;

  typedef struct     packed {
    bit              valid;
    bit              unused;
    map_addr_t       addr;
  } map_mem_t;


  //Classes
  `include "symbol_mapper.svh"

endpackage : symbol_map_pkg