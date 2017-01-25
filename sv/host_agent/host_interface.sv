// ---------------------------------------------------------------------------
//
//  Description: Host Interface
//
// ---------------------------------------------------------------------------
interface host_interface();
  logic         clk;
  logic         reset_n;
  logic         in_config_valid;
  logic [255:0] in_config_data;
  logic         in_config_accept;
endinterface : host_interface
