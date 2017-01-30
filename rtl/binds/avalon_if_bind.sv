// ---------------------------------------------------------------------------
//
//  Description: Avalon Interface Bind/Assertions
//
// ---------------------------------------------------------------------------
`timescale 1ps/1ps

// If we're using the simulator, use UVM reporting structure. Otherwise, just use $error calls
`ifdef SIM_ONLY
  import uvm_pkg::*;
  `define assert_prop_default_avl(check, pa, msg) \
   ERROR_``check``: assert property (@(posedge clk) disable iff (!reset_n) (pa)) else \
                                    uvm_report_error("avalon_if_bind", $sformatf("(%m) %s : %s",`"``check``: `",msg));

  `define assert_prop_clkrst_avl(check, pa, msg, dc, clk) \
   ERROR_``check``: assert property (@(posedge clk) disable iff (dc) (pa)) else \
                                    uvm_report_error("avalon_if_bind", $sformatf("(%m) %s : %s",`"``check``: `",msg));
`else
  `define assert_prop_default_avl(check, pa, msg) \
   ERROR_``check``: assert property (@(posedge clk) disable iff (!reset_n) (pa)) else $error("%s",{`"``check``: `",msg});
`endif

// Convenience macros to define cover properties of different types (with/without reset, disable condition, etc.)
`define cover_prop_default(check, pc) \
``check``: cover property (@(posedge clk) disable iff (!reset_n) (pc));

`define cover_prop_clkrst(check, pc, dc, clk) \
``check``: cover property (@(posedge clk) disable iff (dc) (pc));

`define cover_point_default(check, pc) \
``check``: coverpoint pc iff (reset_n);

`define cover_point_clkrst(check, pc, dc) \
``check``: coverpoint pc iff (dc);

// This interface is intended to be bound into any Avalon interface signal bundle for signal-level checking
// and coverage collection
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
      if (valid) begin
        if (startofpacket && !in_pkt) begin
          in_pkt <= 1'b1;
        end else if (in_pkt && endofpacket) begin
          in_pkt <= 1'b0;
        end
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

  // Error signal should never go high in this environment
  `assert_prop_default_avl(assert_invalid_error,
                      (!error),
                      "Error asserted")

  // ReadLatency of 1, i.e. if ready goes low, valid must drop one cycle later
  `assert_prop_default_avl(valid_deassert,
                      (!ready |-> ##1 !valid),
                      "Valid did not de-assert the clock after read de-asserted")

  // Problem if we see EOP rise unless we are in a packet
  `assert_prop_default_avl(invalid_eop,
                      ((endofpacket && valid) |->  (in_pkt || startofpacket)),
                      "EOP asserted while not in packet")

  // Problem if we see valid active unless we are in a packet or we're starting a packet
  `assert_prop_default_avl(invalid_valid,
                      (valid |-> (in_pkt || startofpacket)),
                      "Valid asserted outside of packet")

  //------------------------------------------------------------------------------------
  // Embedded coverage
  //------------------------------------------------------------------------------------
  covergroup cg_avalon_fields @(posedge clk);

    // All possible values of empty
    cp_empty: coverpoint empty iff (reset_n) {
      bins MIN       = {'h0                    };
      bins MID       = {[1:(2**EMPTY_WIDTH-2)] };
      bins MAX       = {(2**EMPTY_WIDTH-1)     };
    }

    // All possible ready stall lengths
    cp_rdy_stall_cnt: coverpoint rdy_stall_cnt iff (reset_n) {
      bins MIN       = {'h1                        };
      bins MID       = {[2:(DUT_PIPELINE_DEPTH-1)] };
      bins MAX       = {DUT_PIPELINE_DEPTH         };
    }

    // All possible valid stall lengths
    cp_vld_stall_cnt: coverpoint vld_stall_cnt iff (reset_n) {
      bins MIN       = {'h1                        };
      bins MID       = {[2:(DUT_PIPELINE_DEPTH-1)] };
      bins MAX       = {DUT_PIPELINE_DEPTH         };
    }

   endgroup: cg_avalon_fields
   cg_avalon_fields cg_avalon_fields_inst=new;

   // Cover property definitions

   // Two back-to-back valid beats
  `cover_prop_default(b2b_beats,
              ( ready && valid |-> ##1 ready && valid))

  // Generated a single-beat packet (SOP and EOP on same cycle)
  `cover_prop_default(single_cycle_pkt,
              (startofpacket && endofpacket && ready && valid))

  // Generated a double-beat packet (SOP immediately followed by EOP)
  `cover_prop_default(min_pkt_size,
              ( startofpacket |-> ##1 endofpacket))

  // Single-cycle stall between packets
  `cover_prop_default(single_cycle_stall_between_packets,
              ( startofpacket |-> ##2 endofpacket))

  // Back-to-back packets, i.e. EOP followed by an SOP on next cycle
  `cover_prop_default(b2b_pkt,
              ( endofpacket |-> ##1 startofpacket))

  // Two two-beat packets back-to-back
  `cover_prop_default(b2b_min_pkt,
              ( startofpacket |-> ##1 endofpacket |-> ##1 startofpacket |-> ##1 endofpacket))

  // Stall with ready drop during SOP
  `cover_prop_default(dest_stall_sop,
              ( startofpacket |-> !ready))

  // Stall with ready drop during EOP
  `cover_prop_default(dest_stall_eop,
              ( endofpacket |-> !ready))

  // Stall at any point during packet
  `cover_prop_default(dest_stall_in_pkt,
              ( in_pkt |-> !ready))

  // Stall via valid drop within packet
  `cover_prop_default(source_stall_in_pkt,
              ( in_pkt |-> !valid && ready))

  initial begin
    $display("INFO: avalon_if_bind file (%m) loaded");
  end

endinterface : avalon_if_bind

// Bind it
bind avalon_if avalon_if_bind #(DATA_WIDTH, EMPTY_WIDTH) avalon_if_bound (.*);