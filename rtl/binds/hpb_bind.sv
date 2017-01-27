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

interface hpb_bind #(
  parameter HPB_DATA_WIDTH = 128,
  parameter HPB_ASYNC_HOST = 0
) (
   input                      clk,
   input                      reset_n,
   input    t_host_msg_map    host_msg_map,
   host_interface             host_interface_synced
);

  reg config_vld_q;

  // get registered version of config valid because host_msg_map is registered
  always_ff @(posedge clk) begin
    if (!reset_n) begin
      config_vld_q <= 1'b0;
    end else begin
      config_vld_q <= host_interface_synced.in_config_valid;
    end

  end

  //------------------------------------------------------------------------------------
  // Assertions
  //------------------------------------------------------------------------------------
  `assert_prop_default(assert_invld_byte_en_PRICE,
                      ((host_msg_map.ram == 8'h2 ) |-> (host_msg_map.byte_en == 24'h00_FFFF)),
                      "Invalid BYTE_EN when targeting Price RCB")

  `assert_prop_default(assert_invld_byte_en_VOLUME,
                      ((host_msg_map.ram == 8'h4 ) |-> (host_msg_map.byte_en == 24'h00_00FF)),
                      "Invalid BYTE_EN when targeting Volume RCB")

  `assert_prop_default(assert_invld_byte_en_ORDER,
                      ((host_msg_map.ram == 8'h8 ) |-> (host_msg_map.byte_en == 24'h00_FFFF)),
                      "Invalid BYTE_EN when targeting Order RCB")

  `assert_prop_default(assert_invld_cmd,
                      ((config_vld_q == 1'b1) |-> host_msg_map.cmd == 8'h2),
                      "Host Command != 2 (LOAD) when config valid is high")

  //------------------------------------------------------------------------------------
  // Embedded coverage
  //------------------------------------------------------------------------------------
  covergroup cg_hpb @(posedge clk);

    // TITLE: Cover all states have been hit
    cp_msg_cmd: coverpoint host_msg_map.cmd iff (reset_n) {
      bins LOAD       = {8'h2 };
    }

    // TITLE: Cover all states have been hit
    cp_msg_ram: coverpoint host_msg_map.ram iff (reset_n) {
      bins PRICE      = {8'h2 };
      bins VOLUME     = {8'h4 };
      bins ORDER      = {8'h8 };
      bins SYMBOL     = {8'h1 };
    }


   endgroup: cg_hpb
   cg_hpb cg_hpb_inst=new;


  initial begin
    $display("INFO: hpb_bind file loaded");
  end

endinterface : hpb_bind

// Bind it
bind hpb hpb_bind #(HPB_DATA_WIDTH, HPB_ASYNC_HOST) hpb_bound (.*);