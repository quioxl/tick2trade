`timescale 1ns/1ps
module tb;

  import uvm_pkg::*;
  import avalon_pkg::*;
  import feed_test_pkg::*;

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

  avalon_if avl_slave_if ();
  assign avl_slave_if.clk = clk;
  assign avl_slave_if.reset_n = reset_n;

  // UNTIL DUT IS HERE... TIE MASTER & SLAVE TOGETHER DIRECTLY
  assign avl_master_if.ready = avl_slave_if.ready;
  assign avl_slave_if.valid = avl_master_if.valid;
  assign avl_slave_if.data = avl_master_if.data;
  assign avl_slave_if.startofpacket = avl_master_if.startofpacket;
  assign avl_slave_if.endofpacket = avl_master_if.endofpacket;
  assign avl_slave_if.error = avl_master_if.error;
  assign avl_slave_if.empty = avl_master_if.empty;

  initial begin
    uvm_config_db#(virtual avalon_if)::set(null,"*","master_if",avl_master_if);
    uvm_config_db#(virtual avalon_if)::set(null,"*","slave_if",avl_slave_if);
    run_test();
  end

endmodule