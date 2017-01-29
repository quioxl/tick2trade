// This module takes a record file (produced by avalon_recorder) 
// and re-runs it.  A "done" output is asserted once it has finished
// its work, all signals will be driven to an inactive state at that
// point.
// The input interface expects the clock to be driven, all other master
// driven signaling will be driven by this module.

module avalon_replay #(parameter string fname = "avalon_record.txt") (avalon_if avif, output bit done);

  int fd;
  int count;
  int code;

  initial begin
    done = 0;
    fd = $fopen(fname,"r");
    if (fd==0) $fatal("Unable to open %s in read mode",fname);
    do begin
      @(avif.clk);
      code = $fscanf(fd,"%d:%b %b %b %b %b %b %b",count,
                                                  avif.reset_n,
                                                  avif.valid,
                                                  avif.ready,
                                                  avif.startofpacket,
                                                  avif.endofpacket,
                                                  avif.data,
                                                  avif.empty);
      $display("CODE:%0d",code);
    end while (code==8);
    $fclose(fd);
    avif.reset_n = 1'b1;
    avif.valid = 1'b0;
    avif.ready = 1'b1;
    avif.startofpacket = 1'b0;
    avif.endofpacket = 1'b0;
    avif.data = 'b0;
    avif.empty = 'b0;
    done = 1;
  end

endmodule

