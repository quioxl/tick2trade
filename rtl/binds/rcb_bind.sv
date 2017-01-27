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

interface rcb_bind #(
  parameter RCB_RAM_ADDR_WIDTH = 128,
  parameter RCB_RAM_WIDTH = 0
) (
   input                      clk,
   input                      reset_n,
   input                      sef_read,
   input                      ignore_hpb_wr_req_q,
   hpb_if                     hpb_if_i
);


  //------------------------------------------------------------------------------------
  // Assertions
  //------------------------------------------------------------------------------------
  `assert_prop_default(assert_hpb_wr_done,
                      (hpb_if_i.hpb_wr_req |-> !$isunknown(hpb_if_i.hpb_wr_addr)),
                      "WR Address unknown when wr_request is asserted")

  `assert_prop_default(assert_ignore_deassert,
                      (hpb_if_i.hpb_wr_req |-> ##1 !hpb_if_i.hpb_wr_req |-> ##1 !ignore_hpb_wr_req_q),
                      "Ignore did not de-assert after WR Request de-asserted")

  //------------------------------------------------------------------------------------
  // Embedded coverage
  //------------------------------------------------------------------------------------
  covergroup cg_rcb @(posedge clk);

    // TITLE: Cover all collision scenarios have been hit
    cp_rcb_collision_scenarios: coverpoint {sef_read, hpb_if_i.hpb_wr_req} iff (reset_n) {
      bins WRITE_ONLY    = { 2'b01 };
      bins READ_ONLY     = { 2'b10 };
      bins COLLISION_HIT = { 2'b11 };
    }

    cp_width_param: coverpoint RCB_RAM_WIDTH iff (reset_n) {
      bins W_64      = { 64 } ;
      bins W_128     = { 128 };
    }

   endgroup: cg_rcb
   cg_rcb ccg_rcb_inst=new;


  `cover_prop_default(wr_during_ignore,
              ( hpb_if_i.hpb_wr_req |-> ignore_hpb_wr_req_q))

  initial begin
    $display("INFO: rcb_bind file loaded");
  end

endinterface : rcb_bind

// Bind it
bind rcb rcb_bind #(RCB_RAM_ADDR_WIDTH, RCB_RAM_WIDTH) rcb_bound (.*);