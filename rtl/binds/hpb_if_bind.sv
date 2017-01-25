// ---------------------------------------------------------------------------
//
//  Copyright 2017 IMC. All Rights Reserved.
//
//  Description: Avalon Interface Bind/Assertions
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

module hpb_if_bind
#(
  parameter RCB_RAM_WIDTH  = 64
) (
 input                              clk,
 input                              reset_n,
 input                              hpb_wr_addr,
 input       [(RCB_RAM_WIDTH-1):0]  hpb_wr_data,
 input   [log2(RCB_RAM_WIDTH)-1:0]  hpb_wr_en,
 input                              hpb_wr_req,
 input                              rcb_wr_done

);

  `assert_prop_default(assert_invalid_we,
                      (hpb_wr_req |-> (hpb_wr_en != 'h0)),
                      "Write Request asserted without any write enables")

  initial begin
    $display("INFO: hpb_if_bind file loaded");
  end

endmodule // hpb_if_bind

// Bind it
bind hpb_if hpb_if_bind  hpb_if_bound (.*);