// This module generates a vector-file recording of any activity
// it sees on the attached interface bus.  File name used is 
// parameterizable - be sure to change it if you drop in more than one
// of these modules in the same bench.
module avalon_recorder #(parameter string fname = "avalon_record.txt") (avalon_if avif);

  int fd;
  int count;

  initial begin
    fd = $fopen(fname);
    if (fd==0) $fatal("Unable to open %s",fname);
  end

  always @(avif.clk) begin
    $fwrite(fd,"%0d:%b %b %b %b %b %b\n",count++,
                                         avif.reset_n,
                                         avif.valid,
                                         avif.startofpacket,
                                         avif.endofpacket,
                                         avif.data,
                                         avif.empty);
  end

endmodule
