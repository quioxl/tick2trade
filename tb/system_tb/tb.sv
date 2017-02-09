`timescale 1ns/1ps
module tb;

  parameter HPB_ASYNC_HOST = 0;

  import uvm_pkg::*;
  import avalon_pkg::*;
  import host_agent_pkg::*;
  import order_pkg::*;
  import system_test_pkg::*;

  bit clk;
  bit reset_n;
  bit hpb_clk;
  bit hpb_reset_n;

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
  assign host_if.clk = hpb_clk;
  assign host_if.reset_n = hpb_reset_n;

  generate //Generate to create an async clock if configured to do so
    if (HPB_ASYNC_HOST == 1) begin : host_clk
      initial begin
        hpb_clk = 1'b0;
        forever #6ns hpb_clk = ~hpb_clk;
      end

      initial begin
        hpb_reset_n = 1'b0;
        repeat (10) @(negedge hpb_clk);
        hpb_reset_n = 1'b1;
      end
    end else begin : host_clk
      assign hpb_clk = clk;
      assign hpb_reset_n = reset_n;
    end
  endgenerate

  order_interface order_if ();
  assign order_if.clk = clk;
  assign order_if.reset_n = reset_n;

  // DUT Instantiation (Using default parameters other than async host clock)
  tick2trade #(.HPB_ASYNC_HOST(HPB_ASYNC_HOST)) DUT (
           .clk                (clk),
           .reset_n            (reset_n),
           .aclk               (hpb_clk),
           .areset_n           (hpb_reset_n),
           .dec_in_if          (feed_if),
           .host_if            (host_if),
           .order_if           (order_if)
           );

  initial begin
    $timeformat(-9,5,"ns",7);
    uvm_config_db#(virtual avalon_if)      ::set(null,"*","feed_if", feed_if);
    uvm_config_db#(virtual host_interface) ::set(null,"*","host_if", host_if);
    uvm_config_db#(virtual order_interface)::set(null,"*","order_if", order_if);
    run_test();
  end

  avalon_recorder U_avl_recorder (.avif(feed_if));
  host_recorder U_hst_recorder (.hif(host_if));

endmodule
