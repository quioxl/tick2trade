`timescale 1ns/1ns

module feed_replay_tb ();

  avalon_if avif ();
  wire done;

  initial begin
    avif.clk = 1'b0;
    forever #5ns avif.clk = ~avif.clk;
  end

  feed_decoder DUT (.clk               ( avif.clk           ),
                    .reset_n           ( avif.reset_n       ),
                    .in_ready          (                    ),
                    .in_valid          ( avif.valid         ),
                    .in_startofpacket  ( avif.startofpacket ),
                    .in_endofpacket    ( avif.endofpacket   ),
                    .in_data           ( avif.data          ),
                    .in_empty          ( avif.empty         ),
                    .in_error          ( 1'b0               ),
                    .out_ready         ( avif.ready         ),
                    .out_valid         (                    ),
                    .out_startofpacket (                    ),
                    .out_endofpacket   (                    ),
                    .out_data          (                    ),
                    .out_empty         (                    ),
                    .out_error         (                    ));

  avalon_replay rply (.avif(avif),.done(done));

  initial begin
    $dumpfile("feed.vcd");
    $dumpvars(0);
    wait (done);
    #1us;
    $finish();
  end

endmodule