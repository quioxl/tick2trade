`include "uvm_macros.svh"
package avalon_pkg;
  import uvm_pkg::*;
  typedef enum { AVL_MASTER, AVL_SLAVE } avalon_master_slave_enum;
  `include "avalon_message_seq_item_base.svh"
  `include "avalon_message_seq_item_new.svh"
  `include "avalon_config.svh"
  `include "avalon_master_driver.svh"
  `include "avalon_monitor.svh"
  `include "avalon_seq_base.svh"
endpackage