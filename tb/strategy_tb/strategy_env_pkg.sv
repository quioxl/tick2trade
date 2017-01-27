`include "uvm_macros.svh"
package strategy_env_pkg;
  import uvm_pkg::*;
  import avalon_pkg::*;
  import feed_agent_pkg::*;
  import host_agent_pkg::*;
  import order_pkg::*;
  import symbol_map_pkg::*;

  //typedefs
  typedef struct packed {
    symbol_t     symbol;
    map_addr_t   map_addr;
    bit [31:0]   min_vol;
    bit [31:0]   max_vol;
    bit [63:0]   min_price;
    bit [63:0]   max_price;
    bit [127:0]  order;
    bit          valid;
  } host_order_t;
  
  //Imp decls
  `uvm_analysis_imp_decl(_STRATEGY_ACTUAL)
  `uvm_analysis_imp_decl(_STRATEGY_EXPECT)
  `uvm_analysis_imp_decl(_host)

  //Classes
  `include "strategy_env_config.svh"
  `include "strategy_predictor.svh"
  `include "strategy_scoreboard.svh"
  `include "new_order_generator.svh"
  `include "strategy_env.svh"
  
endpackage : strategy_env_pkg
  