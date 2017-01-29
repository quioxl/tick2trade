// Module replays the contents of a host record output, asserting done output bit
// when complete.

module host_replay #(parameter string fname = "host_record.txt") (host_interface hif, output bit done);

  int fd;
  int count;
  int code;

  initial begin
    done = 0;
    fd = $fopen(fname,"r");
    if (fd==0) $fatal("Unable to open %s in read mode",fname);
    do begin
      @(hif.clk);
      code = $fscanf(fd,"%d:%b %b %b",count,hif.reset_n,hif.in_config_valid,hif.in_config_data);
    end while (code==4);
    $fclose(fd);
    hif.reset_n = 1'b1;
    hif.in_config_valid = 1'b0;
    hif.in_config_data = 'b0;
    done = 1;
  end

endmodule