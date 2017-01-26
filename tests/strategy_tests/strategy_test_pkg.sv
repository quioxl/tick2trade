`include "uvm_macros.svh"
package strategy_test_pkg;
  import uvm_pkg::*;
  import avalon_pkg::*;
  import feed_agent_pkg::*;
  import host_agent_pkg::*;
  import order_pkg::*;
  import strategy_env_pkg::*;
  import strategy_seq_pkg::*;

  `include "strategy_test_base.svh"
  `include "sanity_test.svh"
  `include "basic_test.svh"
endpackage
