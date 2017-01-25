module feed_recorder (avalon_if master_if);

  int fd;
  int count;

  initial begin
    fd = $fopen("feed_record.txt");
    if (fd==0) $fatal("Unable to open feed_record.txt");
  end

  always @(master_if.clk) begin
    $fwrite(fd,"%0d:%b %b %b %b %b %b\n",count++,
                                      master_if.reset_n,
                                      master_if.valid,
                                      master_if.startofpacket,
                                      master_if.endofpacket,
                                      master_if.data,
                                      master_if.empty);
  end

endmodule
