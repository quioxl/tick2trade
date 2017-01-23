/* 
 * This package contains all of the components, transactions and sequences
 * related to the host_agent.  Import this package if you need to use 
 * the host_agent anywhere.
 */

`include "uvm_macros.svh"

package host_agent_pkg;

   import uvm_pkg::*;

   //Typedef used by the host_agent
   typedef enum bit[1:0]  {READ, WRITE, PAUSE} instruction_type;

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
   
