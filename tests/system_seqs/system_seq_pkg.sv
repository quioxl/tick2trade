package system_seq_pkg;
`include "uvm_macros.svh"
  
  import uvm_pkg::*;
  import avalon_pkg::*;
  import feed_agent_pkg::*;
  import host_agent_pkg::*;
  import order_pkg::*;
  import symbol_map_pkg::*;
  import strategy_seq_pkg::*;

/* -----\/----- EXCLUDED -----\/-----
`include "random_host_program_seq.svh"
`include "incr_host_program_seq.svh"
`include "random_feed_traffic_seq.svh"
`include "feed_symbol_match_seq.svh"
 -----/\----- EXCLUDED -----/\----- */

endpackage : system_seq_pkg
  