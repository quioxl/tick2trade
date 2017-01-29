// This module generates a vector-file recording of any activity it sees on the attached
// host bus interface.

module host_recorder #(parameter string fname = "host_record.txt") (host_interface hif);

  int fd;
  int count;

  initial begin
    fd = $fopen(fname);
    if (fd==0) $fatal("Unable to open %s",fname);
  end

  always @(hif.clk) begin
    $fwrite(fd,"%0d:%b %b %b\n",count++,
                      hif.reset_n,
                      hif.in_config_valid,
                      hif.in_config_data);
  end

endmodule