// The feed agent is not a full protocol agent - it is a "layered" agent that leverages
// existing capability in the Avalon agent. This agent builds up a large packet from smaller
// packets of message data, sending the large packet into the avalon agent for actual
// transmission.  In reverse, the monitor in this agent receives large packets from
// the Avalon agent and picks out individual messages, sending those smaller packets out
// on its analysis port.
`include "uvm_macros.svh"
package feed_agent_pkg;
  import uvm_pkg::*;
  import avalon_pkg::*;
  `include "feed_message_item.svh"
  `include "feed_message_to_avalon_seq.svh"
  `include "feed_monitor.svh"
  `include "feed_layering.svh"
  `include "feed_simple_seq.svh"
  `include "feed_random_seq.svh"
endpackage