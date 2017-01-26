package strategy_seq_pkg;
`include "uvm_macros.svh"
  
  import uvm_pkg::*;
  import avalon_pkg::*;
  import feed_agent_pkg::*;
  import host_agent_pkg::*;
  import order_pkg::*;

`include "random_host_program_seq.svh"
`include "random_feed_traffic_seq.svh"

endpackage : strategy_seq_pkg
  