`include "uvm_macros.svh"
package feed_test_pkg;
  import uvm_pkg::*;
  import avalon_pkg::*;
  import feed_env_pkg::*;

  `include "feed_test_base.svh"
  `include "sanity_test.svh"
  `include "feed_random_test.svh"
endpackage
