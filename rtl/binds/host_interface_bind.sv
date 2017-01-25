// ---------------------------------------------------------------------------
//
//  Copyright 2017 IMC. All Rights Reserved.
//
//  Description: Host Interface Bind/Assertions
//
// ---------------------------------------------------------------------------
`timescale 1ps/1ps

`ifdef SIM_ONLY
  import uvm_pkg::*;
  `define assert_prop_default(check, pa, msg) \
   ERROR_``check``: assert property (@(posedge clk) disable iff (!reset_n) (pa)) else \
                                    uvm_report_error("avalon_if_bind", {`"``check``: `",msg});

  `define assert_prop_clkrst(check, pa, msg, dc, clk) \
   ERROR_``check``: assert property (@(posedge clk) disable iff (dc) (pa)) else \
                                    uvm_report_error("avalon_if_bind", {`"``check``: `",msg});
`else
  `define assert_prop_default(check, pa, msg) \
   ERROR_``check``: assert property (@(posedge clk) disable iff (!reset_n) (pa)) else $error("%s",{`"``check``: `",msg});
`endif

module host_interface_bind (

  input         clk,
  input         reset_n,
  input         in_config_valid,
  input [255:0] in_config_data,
  input         in_config_accept

 );

  `assert_prop_default(no_unknown,
                      (!$isunknown(reset_n) && !$isunknown(in_config_valid) &&
                       $isunknown(in_config_data) && !$isunknown(in_config_accept)),
                      "One of the host_interface signals is an 'x' or a 'z'.")

  initial begin
    $display("INFO: host_interface_bind file loaded");
  end

endmodule

// Bind it
bind host_interface host_interface_bind host_interface_bound (.*);