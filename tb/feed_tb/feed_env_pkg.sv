`include "uvm_macros.svh"
package feed_env_pkg;
  import uvm_pkg::*;
  import avalon_pkg::*;
  import feed_agent_pkg::*;

  `uvm_analysis_imp_decl(_FEED_ACTUAL)
  `uvm_analysis_imp_decl(_FEED_EXPECT)

  `include "feed_env_config.svh"
  `include "feed_predictor.svh"
  `include "feed_scoreboard.svh"
  `include "feed_env.svh"
endpackage