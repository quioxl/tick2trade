`include "uvm_macros.svh"

/* a description of the wires used to connect the DUT to the testbench */
interface host_interface();
  import uvm_pkg::*;
  import host_agent_pkg::*;

  logic         clk;
  logic         reset_n;
  logic         in_config_valid;
  logic [255:0] in_config_data;
  logic         in_config_accept;

  //Bus Protocol Assertions
  property no_unknown;
    @(posedge clk) !$isunknown(reset_n) && !$isunknown(in_config_valid) && 
      !$isunknown(in_config_data) && !$isunknown(in_config_accept);
  endproperty : no_unknown
  
  assert_all_is_known : assert property(no_unknown) else
    `uvm_error("ISUNKNOWN", "One of the host_interface signals is an 'x' or a 'z'.")
  
      
endinterface : host_interface
