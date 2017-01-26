`timescale 1ns/1ps
module tb;

  import uvm_pkg::*;
  import avalon_pkg::*;
  import host_agent_pkg::*;
  import order_pkg::*;
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

  avalon_if feed_if ();
  assign feed_if.clk = clk;
  assign feed_if.reset_n = reset_n;

  host_interface host_if ();
  assign host_if.clk = clk;
  assign host_if.reset_n = reset_n;

  order_interface order_if ();
  assign order_if.clk = clk;
  assign order_if.reset_n = reset_n;

  // DUT Instantiation (Using default parameters)
  tts DUT (
           .clk                (clk),
           .reset_n            (reset_n),
           .feed_if            (feed_if),
           .host_interface_in  (host_if),
           .order_if           (order_if)
           );

  initial begin
    uvm_config_db#(virtual avalon_if)      ::set(null,"*","feed_if", feed_if);
    uvm_config_db#(virtual host_interface) ::set(null,"*","host_if", host_if);
    uvm_config_db#(virtual order_interface)::set(null,"*","order_if", order_if);
    run_test();
  end

endmodule