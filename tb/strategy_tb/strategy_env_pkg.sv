`include "uvm_macros.svh"
package strategy_env_pkg;
  import uvm_pkg::*;
  import avalon_pkg::*;
  import host_agent_pkg::*;
  import symbol_map_pkg::*;

  //typedefs
  typedef struct packed {
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
  //`include "strategy_message_item.svh"
  //`include "strategy_message_to_avalon_seq.svh"
  `include "strategy_env_config.svh"
  `include "strategy_predictor.svh"
  //`include "strategy_layering.svh"
  //`include "strategy_monitor.svh"
  //`include "strategy_scoreboard.svh"
  `include "strategy_env.svh"
  //`include "strategy_simple_seq.svh"
endpackage : strategy_env_pkg
  