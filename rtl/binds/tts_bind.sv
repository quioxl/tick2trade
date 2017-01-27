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

`define cover_prop_default(check, pc) \
``check``: cover property (@(posedge clk) disable iff (!reset_n) (pc));

`define cover_prop_clkrst(check, pc, dc, clk) \
``check``: cover property (@(posedge clk) disable iff (dc) (pc));

`define cover_point_default(check, pc) \
``check``: coverpoint pc iff (reset_n);

`define cover_point_clkrst(check, pc, dc) \
``check``: coverpoint pc iff (dc);

import tts_pkg::*;

interface tts_bind (
   input             clk,
   input             reset_n,
   input      [2:0]  sym_idx,
   input             sef_out_valid,
   input             vcmp_pass,
   input             pcmp_pass


);


  //------------------------------------------------------------------------------------
  // Assertions
  //------------------------------------------------------------------------------------


  //------------------------------------------------------------------------------------
  // Embedded coverage
  //------------------------------------------------------------------------------------
  covergroup cg_tts @(posedge clk);

    cp_sym_idx: coverpoint sym_idx iff (reset_n) {
      bins IDX_ZERO    = { 2'b00 };
      bins IDX_ONE     = { 2'b01 };
      bins IDX_TWO     = { 2'b10 };
      bins IDX_THREE   = { 2'b11 };
    }

    cp_cmp_results: coverpoint {vcmp_pass, pcmp_pass} iff (reset_n && sef_out_valid) {
      bins BOTH_MISCOMP  = { 2'b00 };
      bins PCMP_ONLY     = { 2'b01 };
      bins VCMP_ONLY     = { 2'b10 };
      bins BOTH_CMP_OK   = { 2'b11 };
    }

   endgroup: cg_tts
   cg_tts cg_tts_inst=new;

  initial begin
    $display("INFO: tts_bind file loaded");
  end

endinterface : tts_bind

// Bind it
bind tts tts_bind tts_bound (.*);