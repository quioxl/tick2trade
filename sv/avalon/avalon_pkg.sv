// Avalon protocol package - see included file contents for more detail

`include "uvm_macros.svh"
package avalon_pkg;
  import uvm_pkg::*;
  typedef enum { AVL_MASTER, AVL_SLAVE } avalon_master_slave_enum;
  `include "avalon_seq_item_base.svh"
  `include "avalon_message_item.svh"
  `include "avalon_config.svh"
  `include "avalon_driver_base.svh"
  `include "avalon_master_driver.svh"
  `include "avalon_slave_driver.svh"
  `include "avalon_monitor.svh"
  `include "avalon_seq_base.svh"
  `include "avalon_random_seq.svh"
  `include "avalon_agent.svh"
endpackage