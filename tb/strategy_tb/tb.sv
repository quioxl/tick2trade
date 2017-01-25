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

  // DUT Instantiation (Using default parameters)
  tts DUT (
           .feed_if (avl_master_if),
           .host_if (host_if)
           );

  initial begin
    uvm_config_db#(virtual avalon_if)::set(null,"*","avl_master_if",avl_master_if);
    uvm_config_db#(virtual host_interface)::set(null,"*","host_if", host_if);
    run_test();
  end

endmodule