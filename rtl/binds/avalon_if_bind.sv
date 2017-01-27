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

  localparam DUT_PIPELINE_DEPTH = 10;

  reg       in_pkt;
  reg [4:0] rdy_stall_cnt;
  reg [4:0] vld_stall_cnt;

  // In packet identification logic
  always_ff @(posedge clk) begin
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

  // Ready Stall counter
  always_ff @(posedge clk) begin
    if (!reset_n) begin
      rdy_stall_cnt <= 1'b0;
    end else begin
      if (in_pkt) begin
        if (!ready) begin
          rdy_stall_cnt <= rdy_stall_cnt +1;
        end else begin
          rdy_stall_cnt <= 'h0;
        end
      end else if (in_pkt && endofpacket) begin
        rdy_stall_cnt <= 'h0;
      end
    end
  end

  // Valid Stall counter
  always_ff @(posedge clk) begin
    if (!reset_n) begin
      vld_stall_cnt <= 1'b0;
    end else begin
      if (in_pkt) begin
        if (!ready) begin
          vld_stall_cnt <= vld_stall_cnt +1;
        end else begin
          vld_stall_cnt <= 'h0;
        end
      end else if (in_pkt && endofpacket) begin
        vld_stall_cnt <= 'h0;
      end
    end
  end

  //------------------------------------------------------------------------------------
  // Assertions
  //------------------------------------------------------------------------------------
  `assert_prop_default(assert_invalid_eop,
                      (endofpacket |-> valid),
                      "EOP asserted without valid")

  `assert_prop_default(assert_invalid_error,
                      (!error),
                      "EOP asserted without valid")

  `assert_prop_default(valid_deassert,
                      (!ready |-> ##1 !valid),
                      "Valid did not de-assert the clock after read de-asserted")

  `assert_prop_default(invalid_eop,
                      (endofpacket |->  in_pkt),
                      "EOP asserted while not in packet")

  //------------------------------------------------------------------------------------
  // Embedded coverage
  //------------------------------------------------------------------------------------
  covergroup cg_avalon_fields @(posedge clk);

    // TITLE: Cover all states have been hit
    cp_empty: coverpoint empty iff (reset_n) {
      bins MIN       = {'h0                    };
      bins MID       = {[1:(2**EMPTY_WIDTH-2)] };
      bins MAX       = {(2**EMPTY_WIDTH-1)     };
    }

    cp_rdy_stall_cnt: coverpoint rdy_stall_cnt iff (reset_n) {
      bins MIN       = {'h1                        };
      bins MID       = {[2:(DUT_PIPELINE_DEPTH-1)] };
      bins MAX       = {DUT_PIPELINE_DEPTH         };
    }

    cp_vld_stall_cnt: coverpoint vld_stall_cnt iff (reset_n) {
      bins MIN       = {'h1                        };
      bins MID       = {[2:(DUT_PIPELINE_DEPTH-1)] };
      bins MAX       = {DUT_PIPELINE_DEPTH         };
    }

   endgroup: cg_avalon_fields
   cg_avalon_fields cg_avalon_fields_inst=new;

  `cover_prop_default(b2b_beats,
              ( ready && valid |-> ##1 ready && valid))

  `cover_prop_default(min_pkt_size,
              ( startofpacket |-> ##1 endofpacket))

  `cover_prop_default(single_cycle_stall_between_packets,
              ( startofpacket |-> ##2 endofpacket))

  `cover_prop_default(b2b_pkt,
              ( endofpacket |-> ##1 startofpacket))

  `cover_prop_default(b2b_min_pkt,
              ( startofpacket |-> ##1 endofpacket |-> ##1 startofpacket |-> ##1 endofpacket))

  `cover_prop_default(dest_stall_sop,
              ( startofpacket |-> !ready))

  `cover_prop_default(dest_stall_eop,
              ( endofpacket |-> !ready))

  `cover_prop_default(dest_stall_in_pkt,
              ( in_pkt |-> !ready))

  `cover_prop_default(source_stall_in_pkt,
              ( in_pkt |-> !valid))

  initial begin
    $display("INFO: avalon_if_bind file loaded");
  end

endinterface : avalon_if_bind

// Bind it
bind avalon_if avalon_if_bind #(DATA_WIDTH, EMPTY_WIDTH) avalon_if_bound (.*);