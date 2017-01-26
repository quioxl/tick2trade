// ---------------------------------------------------------------------------
//
//  Description: Performs the async crossing between Host CFG Clock and
//               core clock
//
// ---------------------------------------------------------------------------

import tts_pkg::*;

module hpb_sync (

  // Clk/Reset
  input                                   clk,                   // Core clock
  input                                   reset_n,               // Active low core reset

  input                                   aclk,                  // Host Async Clk
  input                                   areset_n,              // Host Async Reset

  // Feed Decoder IF
  host_interface                          host_interface_in,     // Host Interface on Async Clock
  host_interface                          host_interface_synced  // Host IF synchronized to core clock

);

  // Tied off now.  Put async in if time allows
  always_comb begin
    host_interface_synced.clk              = host_interface_in.clk;
    host_interface_synced.reset_n          = host_interface_in.reset_n;
    host_interface_synced.in_config_valid  = host_interface_in.in_config_valid;
    host_interface_synced.in_config_data   = host_interface_in.in_config_data;
    host_interface_synced.in_config_accept = host_interface_in.in_config_accept;
  end
endmodule // hpb_sync