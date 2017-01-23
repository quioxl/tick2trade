/* 
 * This package contains all of the components, transactions and sequences
 * related to the host_agent.  Import this package if you need to use 
 * the host_agent anywhere.
 */

`include "uvm_macros.svh"

package host_agent_pkg;

  import uvm_pkg::*;
  
  //Typedefs used by the host_agent
  typedef enum bit[7:0] {INIT_MEM, SYM_DEL, SYM_0, SYM_1} access_type;
  //These structs enable easier construction of data when constructing a symbol
  // portion 0 or a symbol portion 1 message in a sequence
  typedef struct packed {
    bit [15:0]   symbol;
    access_type  acc_type;
    bit [39:0]   unused0;
    bit [31:0]   min_vol;
    bit [31:0]   max_vol;
    bit [63:0]   min_price;
    bit [63:0]   max_price;
  } data_sym_0_t;
  
  typedef struct packed {
    bit [15:0]   symbol;
    access_type  acc_type;
    bit [103:0]  unused0;
    bit [127:0]  order_info;
  } data_sym_1_t;
  
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
   

endpackage : host_agent_pkg
   
