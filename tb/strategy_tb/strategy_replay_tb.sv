`timescale 1ns/1ns
module strategy_replay_tb ();

  host_interface hif ();
  avalon_if avif ();
  order_interface oif ();
  bit clk;

  wire avl_done, hst_done;

  initial begin
    clk = 1'b0;
    forever #5ns clk = ~clk;
  end

  assign hif.clk = clk;
  assign avif.clk = clk;
  assign oif.clk = clk;
  assign oif.reset_n = avif.reset_n;
  assign oif.ready = 1'b1;

  tts DUT (
           .clk                (clk),
           .reset_n            (avif.reset_n),
           .dec_if             (avif),
           .host_if            (hif),
           .order_if           (oif)
           );

  avalon_replay avl_rply (.avif(avif),.done(avl_done));
  host_replay hst_rply (.hif(hif),.done(hst_done));

  initial begin
    $dumpfile("strategy.vcd");
    $dumpvars(0);
    wait (avl_done && hst_done);
    #1us;
    $finish();
  end

endmodule
