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

interface cmp_bind #(
  parameter CMP_RAM_WIDTH  = 64,
  parameter CMP_CYCA_WIDTH = 24,
  parameter CMP_REG_CYCB   = 0,
  parameter CMP_PIPE       = 0,
  parameter FLD_HI         = 0,
  parameter FLD_LO         = 0

) (
  input                              clk,         // Core clock
  input                              reset_n,     // Active low core reset

  input  bit [CMP_RAM_WIDTH-1    :0] rcb_data,    // Parameter constraints
  input  bit [(CMP_RAM_WIDTH/2)-1:0] tts_field,   // Field for compare

  input  bit                         sef_load_a,  // Load the first part of the tts_field
  input  bit                         sef_load_b,  // Load the second part of the tts_field

  input  bit                         cmp_pass,     // Comp values pass the strategy check

  input  bit              [FLD_HI:0] field_q,

  input                              load_b_q,
  input  bit              [FLD_HI:0] compare_val,

  input                              field_lt_max,
  input                              field_gt_min



);


  //------------------------------------------------------------------------------------
  // Assertions
  //------------------------------------------------------------------------------------
  `assert_prop_default(assert_loadA_to_loadB,
                      (sef_load_a |-> !sef_load_b),
                      "Load B asserted with Load A")  // FIXME - im sure there is a way to these two in one argument

  `assert_prop_default(assert_hpb_wr_done,
                      (sef_load_b |-> !sef_load_a),
                      "Load A asserted with Load B")


  //------------------------------------------------------------------------------------
  // Embedded coverage
  //------------------------------------------------------------------------------------
  covergroup cg_cmp @(posedge clk);

    // TITLE: Cover all collision scenarios have been hit
    cp_param_cycb: coverpoint CMP_REG_CYCB iff (reset_n) {
      bins VOL    = { 0};
      bins PRICE  = { 1 };
    }

    cp_cmp_results: coverpoint {field_lt_max,field_gt_min} iff (reset_n) {
      bins ABOVE_MAX    = { 2'b01 };
      bins CMP_OK       = { 2'b11 };
      bins BELOW_MIN    = { 2'b10 };
    }

   endgroup: cg_cmp
   cg_cmp cg_cmp_inst=new;


  `cover_prop_default(b2b_compare_pass,
              ( cmp_pass |-> ##1 cmp_pass))

  initial begin
    $display("INFO: cmp_bind file loaded");
  end

endinterface : cmp_bind

// Bind it
bind cmp cmp_bind #(CMP_RAM_WIDTH, CMP_CYCA_WIDTH, CMP_REG_CYCB, CMP_PIPE, FLD_HI, FLD_LO) cmp_bound (.*);