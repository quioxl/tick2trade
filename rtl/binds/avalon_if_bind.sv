// ---------------------------------------------------------------------------
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

interface avalon_if_bind #( parameter DATA_WIDTH = 64, 
                            parameter EMPTY_WIDTH = 3) (

   input                     clk,
   input                     reset_n,
   input                     ready,
   input                     valid,
   input                     startofpacket,
   input                     endofpacket,
   input [(DATA_WIDTH-1):0]  data,
   input [(EMPTY_WIDTH-1):0] empty,
   input                     error

 );

  reg in_pkt;

  // In packet identification logic
  always @(posedge clk) begin
    if (!reset_n) begin
      in_pkt <= 1'b0;
    end else begin
      if (startofpacket) begin
         in_pkt <= 1'b1;
      end else if (in_pkt && endofpacket) begin
        in_pkt <= 1'b0;
      end
    end
  end

  `assert_prop_default(assert_invalid_eop,
                      (valid |-> ##1 endofpacket),
                      "EOP asserted without valid")

  `assert_prop_default(assert_invalid_error,
                      (error),
                      "EOP asserted without valid")

  `assert_prop_default(valid_deassert,
                      (!ready |-> ##1 !valid),
                      "Valid did not de-assert the clock after read de-asserted")

  initial begin
    $display("INFO: avalon_if_bind file loaded");
  end

endinterface : avalon_if_bind

// Bind it
bind avalon_if avalon_if_bind #(DATA_WIDTH, EMPTY_WIDTH) avalon_if_bound (.*);