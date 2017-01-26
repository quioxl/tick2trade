/* 
 * This package contains all of the components, transactions and sequences
 * related to the host_agent.  Import this package if you need to use 
 * the host_agent anywhere.
 */

`include "uvm_macros.svh"

package host_agent_pkg;

  import uvm_pkg::*;
  import symbol_map_pkg::*;
  
  //Typedefs used by the host_agent
  // Enum to select the command
  typedef enum bit[7:0] {RESET = 8'h01,
                         LOAD  = 8'h02} cmd_t;
  // Enum to select the memory
  typedef enum bit[7:0] {SYMBOL = 8'h01,
                         PRICE  = 8'h02,
                         VOLUME = 8'h04,
                         ORDER  = 8'h08} ram_t;
  //These structs enable easier construction of data when constructing a symbol
  // portion 0 or a symbol portion 1 message in a sequence
  typedef struct packed {
    cmd_t        cmd;
    ram_t        ram;
    bit [15:0]   addr;
    bit [7:0]    res;
    bit [23:0]   byte_en;
    bit [63:0]   unused;
    bit [127:0]  data;
  } host_trans_t;
  
   //Include the sequence_items (transactions)
`include "host_item.svh"

   //Include the agent config object
`include "host_config.svh"

   //Include the components
`include "host_driver.svh"
`include "host_monitor.svh"
//Create a typedef for the host_sequencer since there is no need to extend the
// uvm_sequencer class
typedef uvm_sequencer #(host_item) host_sequencer;
`include "host_agent.svh"

   //Include the API sequences
`include "host_symbol_seq.svh"

endpackage : host_agent_pkg
   
