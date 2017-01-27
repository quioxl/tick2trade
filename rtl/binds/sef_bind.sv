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

interface sef_bind (
   input                      clk,
   input                      reset_n,
   input   t_sef_st           state,
   avalon_if                  dec_if
);


  //------------------------------------------------------------------------------------
  // Assertions
  //------------------------------------------------------------------------------------
//  `assert_prop_default(assert_hpb_wr_done,
//                      (hpb_if_i.hpb_wr_req |-> !$isunknown(hpb_if_i.hpb_wr_addr)),
//                      "WR Address unknown when wr_request is asserted")
//
//  `assert_prop_default(assert_ignore_deassert,
//                      (hpb_if_i.hpb_wr_req |-> ##1 !hpb_if_i.hpb_wr_req |-> ##1 !ignore_hpb_wr_req_q),
//                      "Ignore did not de-assert after WR Request de-asserted")

  //------------------------------------------------------------------------------------
  // Embedded coverage
  //------------------------------------------------------------------------------------
  covergroup cg_sef @(posedge clk);

    // TITLE: Cover all collision scenarios have been hit
    cp_sef_state: coverpoint state iff (reset_n) {
      bins WAIT   = { tts_pkg::WAIT };
      bins LD     = { tts_pkg::LD   };
      bins CMP    = { tts_pkg::CMP  };
    }

   endgroup: cg_sef
   cg_sef cg_sef_inst=new;


//  `cover_prop_default(wr_during_ignore,
//              ( hpb_if_i.hpb_wr_req |-> ignore_hpb_wr_req_q))

  initial begin
    $display("INFO: sef_bind file loaded");
  end

endinterface : sef_bind

// Bind it
bind sef sef_bind sef_bound (.*);