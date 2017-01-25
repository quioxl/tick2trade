`timescale 1ns/1ps
module tb;

  import uvm_pkg::*;
  import avalon_pkg::*;
  import host_agent_pkg::*;
  import strategy_test_pkg::*;

  bit clk;
  bit reset_n;

  initial begin
    clk = 1'b0;
    forever #5ns clk = ~clk;
  end

  initial begin
    reset_n = 1'b0;
    repeat (10) @(negedge clk);
    reset_n = 1'b1;
  end

  avalon_if avl_master_if ();
  assign avl_master_if.clk = clk;
  assign avl_master_if.reset_n = reset_n;

  host_interface host_if ();
  assign host_if.clk = clk;
  assign host_if.reset_n = reset_n;

  // DUT Instantiation
/* -----\/----- EXCLUDED -----\/-----
  strategy #(.C_PKT_BEAT_BYTES(8),
                 .C_PKT_MAX_BYTES(1500),
                 .C_MSG_CNT_BYTES(2),
                 .C_MSG_LEN_BYTES(2),
                 .C_MSG_MIN_BYTES(8),
                 .C_MSG_MAX_BYTES(32)) DUT (
    .clk                ( clk                         ),
    .reset_n            ( reset_n                     ),
    .in_ready           ( avl_master_if.ready         ),
    .in_valid           ( avl_master_if.valid         ),
    .in_startofpacket   ( avl_master_if.startofpacket ),
    .in_endofpacket     ( avl_master_if.endofpacket   ),
    .in_data            ( avl_master_if.data          ),
    .in_empty           ( avl_master_if.empty         ),
    .in_error           ( avl_master_if.error         ),
    .out_ready          ( avl_slave_if.ready          ),
    .out_valid          ( avl_slave_if.valid          ),
    .out_startofpacket  ( avl_slave_if.startofpacket  ),
    .out_endofpacket    ( avl_slave_if.endofpacket    ),
    .out_data           ( avl_slave_if.data           ),
    .out_empty          ( avl_slave_if.empty          ),
    .out_error          ( avl_slave_if.error          )
  );
 -----/\----- EXCLUDED -----/\----- */

  initial begin
    uvm_config_db#(virtual avalon_if)::set(null,"*","avl_master_if",avl_master_if);
    uvm_config_db#(virtual host_interface)::set(null,"*","host_if", host_if);
    run_test();
  end

endmodule